{-# OPTIONS --allow-unsolved-metas #-}

module Tactic where

open import Data.Nat using (ℕ ; _+_ ; _∸_)
open import Data.Unit using (⊤ ; tt)
open import Level using (zero)
open import Data.Bool hiding (_≟_)
open import Data.List
import Data.List.Categorical
open import Data.Product using (_×_ ; _,_ ; proj₁ ; proj₂ ; map₂ )
open import Function.Base
open import Reflection hiding (_≟_)
open import Reflection.Argument hiding (map)
open import Reflection.DeBruijn
open import Reflection.Instances
open import Reflection.Term hiding (_≟_)
open import Relation.Binary.TypeClasses
open import Relation.Nullary using (does)
open import Reflection.Show using (showName)
open import Reflection.TypeChecking.Monad.Categorical using (applicative)
open import Reflection.TypeChecking.Monad.Syntax hiding (pure)
open import Relation.Binary.PropositionalEquality
            using (cong ; refl ; trans)

open Data.List.Categorical.TraversableA {f = zero} (applicative)

open import Tools
open import Substitution
open import Lemmas

-- TODO: Could instead check if its unifiable with ∀ {Κ}. Κ ++ resCtx
-- Checks whether an argument type is a n-weakened resCtx / inherits resCtx.
inheritsScope : ℕ → Type → Name → Arg Type → Bool
inheritsScope ctxIx resCtx tmName (arg _ (def₂ dName ctxs _)) =
  does (dName ≟ tmName) ∧ isWeakened (weaken ctxIx ctxs)
  where
    isWeakened : Type → Bool
    isWeakened typ =
      if does (typ ≟ resCtx)
      then true
      else case typ of λ
          { (con (quote List._∷_) (_ ⟅∷⟆ _ ⟅∷⟆ _ ⟨∷⟩ ctxs ⟨∷⟩ []))
                 → isWeakened ctxs
          ; _    → false
          }
inheritsScope _ _ _ _ = false

-- Gets the first suitable var constructor.
findVar : Term → List Name → TC Name
findVar varHole conNames = do
  let err = typeErrorS "No suitable var constructor found."
  foldr catchTC err $ flip map conNames $ λ cn →
                      unify varHole (con₀ cn) >> return cn

-- Substitutes references to parameters in a constructor type
-- for some variable in a telescope.
redirectParams : Name → Name → Telescope → ℕ → ℕ → TC Type
redirectParams conName tmName staticTel contextIndex typeIndex = do
  data-type #params _ ← getDefinition tmName
    where _ → typeErrorS "Panic: Tm not data-type"
  inContextTel staticTel $
    let unPi : Type → TC Type
        unPi = λ { (Π[ _ ∶ _ ] rs) → return rs
                 ; _ → typeErrorS "Panic: Parameter but no top pi type."
                 }
    in do
      t ← getType conName >>= normalise
      case #params of λ
        -- No parameters, no need to redirect anything
        { 0 → return t
        -- Context is parameter, redirect to static Γ.
        ; 1 → weaken contextIndex <$> unPi t
        -- Both context and type is parameter, redirect to static Γ, T
        ; 2 → -- Janky substitution
              unPi t <&> weaken (contextIndex ∸ 1) >>= unPi <&> weaken typeIndex
        ; n → typeErrorS "Panic: Too many params"
        }

getVarNameFromTs : Term → TC Name
getVarNameFromTs `ts = normalise (def₁ (quote TermSubst.var) `ts) >>= λ where
  (lam _ (abs _ (lam _ (abs _ (con varName _))))) → return varName
  _ → typeErrorS $ "Panic: Couldn't extract variable name from expected TermSubst record."


module Quoted (`Typ : Type) where
  `Context   = def₁ (quote Context) `Typ
  `Deriv     = def₁ (quote Deriv) `Typ
  `Embed     = def₃ (quote Embed) `Typ
  `Map       = def₄ (quote Map) `Typ

module TS (`Typ : Type) (tmName : Name) (varName : Name) where
  open Quoted `Typ
  `TermSubst = def₃ (quote TermSubst) `Typ
  `extendN   = def₂ (quote Embed.extendN)
  `embed     = def₂ (quote Embed.embed)

  -- The initial, static part of the apply telescope
  staticTel : Telescope
  staticTel =
      ("Dr" , hArg (`Deriv))
    ∷ ("e" , vArg (`Embed (var₀ 0) (def₀ tmName)))
    ∷ ("Γ" , hArg `Context)
    ∷ ("Δ" , hArg `Context)
    ∷ ("m" , vArg (`Map (var₀ 3) (var₀ 1) (var₀ 0)))
    ∷ ("T" , hArg `Typ)
    ∷ []

  buildVarBody : ℕ → Term
  buildVarBody argLen =
    -- Embed.embed e (m x)
    `embed (var₀ (argLen + 4)) (var₁ (argLen + 1) (var₀ 0))

  buildBody : Name → Name
            → List (ℕ × Arg Type) → Type → Term
  buildBody applyName conName argTypes resCtx =
    con conName $ map buildConArg argTypes
    where
      argLen = length argTypes
      `e `m : Term
      `e = weaken argLen (var₀ 4)
      `m = weaken argLen (var₀ 1)
      -- TODO: hArg ↦ unknown is maybe a problem? Γ, A could be visible
      -- Makes the ix:th constructor in the clause body.
      buildConArg : (ℕ × Arg Type) → Arg Term
      buildConArg (ix , vArg t) = vArg $
        if inheritsScope (ix + 1) resCtx tmName (vArg t)
        then def₃ applyName `e (`extendN `e `m) (var₀ ix)
        else var₀ ix
      buildConArg (_ , arg ai _) = arg ai unknown

  buildClause : Name → Name → TC Clause
  buildClause applyName conName = do
    -- If a data type argument is a parameter,
    -- then we need to "redirect" the constructor argument
    -- to the corresponding one in the apply function.
    conTyp ← redirectParams conName tmName staticTel 3 0

    -- conTel is the dynamic part of the telescope,
    -- which we get by decomposing the Tm constructor.
    conTel , (def₂ _ resCtx resTyp) ← return $ telView conTyp
      where _ → typeErrorS "Constructor doesn't produce Tm"

    let tel : Telescope
        tel = staticTel ++ conTel

    let pat : List (Arg Pattern)
        pat = weakenPats (length conTel) (telePat staticTel)
              ++ [ vArg (con conName (telePat conTel)) ]

    -- Constructor argument types and their de Bruijn indices in tel / conTel.
    -- Assumes all constructor args correspond to exactly one variable in pat.
    let argTypes : List (ℕ × Arg Type)
        argTypes = reverseCount (map proj₂ conTel)

    let body : Term
        body = if does (conName ≟ varName)
               then buildVarBody (length conTel)
               else buildBody applyName conName argTypes resCtx

    return (clause tel pat body)

  buildApply : Term → List Name → TC ⊤
  buildApply applyHole conNames = do
    applyName ← freshName "applyGenerated"
    inferType applyHole >>= declareDef (vArg applyName)

    -- TODO: Prepend constructor name to error stack?
    clauses ← forA conNames $ buildClause applyName

    defineFun applyName clauses
    unify applyHole (def₀ applyName)


deriveSubst' : ∀ {Ty} {Tm : Deriv Ty} → Term → TC ⊤
deriveSubst' {Typ} {Tm} tsHole = do
  `Typ ← quoteTC Typ
  `Tm ← quoteTC Tm
  checkType tsHole (def₂ (quote TermSubst) `Typ `Tm)

  (def₀ tmName) ← normalise `Tm
    where _ → typeErrorS "Couldn't infer Tm to a be concrete data type."

  varHole ← newMeta!
  applyHole ← newMeta!
  tsCon ← recordConstructor $ quote TermSubst
  unify tsHole $ con₂ tsCon varHole applyHole

  conNames ← getConstructors tmName
  varName ← findVar varHole conNames
  TS.buildApply `Typ tmName varName applyHole conNames

  return tt

macro deriveSubst = deriveSubst'

module LA where
  buildClause : Type → Name → Name → Name → Telescope
              → ((argLen : ℕ) → Term)
              → ((argLen : ℕ) (ix : ℕ) (funName : Name) → Term)
              → ℕ → ℕ → Name → TC Clause
  buildClause `Typ tmName varName funName staticTel
              varBody inheritTerm resCtxIx resTypeIx conName = do
    conTyp ← redirectParams conName tmName staticTel resCtxIx resTypeIx

    conTel , (def₂ _ resCtx resTyp) ← return $ telView conTyp
      where _ → typeErrorS $ "Constructor doesn't produce Tm"

    let tel : Telescope
        tel = staticTel ++ conTel

    let pat : List (Arg Pattern)
        pat = weakenPats (length conTel) (telePat staticTel)
              ++ [ vArg (con conName (telePat conTel)) ]

    -- Pairs of visible constructor arguments and their de Bruijn indices
    let visibleArgTypes : List (ℕ × Type)
        visibleArgTypes = map (map₂ unArg)
                        ∘ boolFilter (λ {(_ , vArg _) → true ; _ → false })
                        ∘ reverseCount
                        $ map proj₂ conTel

    let conArgLen = length conTel

    -- Used for congₙ
    `vArgLen ← quoteTC $ length visibleArgTypes

    -- Assuming just apply args + constructor args are in scope
    let body : Term
        body = if does (conName ≟ varName)
               then varBody conArgLen
               else buildBody conArgLen `vArgLen visibleArgTypes resCtx

    return (clause tel pat body)

    where
      -- TODO: Congₙ only supports explicit arguments.
      buildBody : ℕ → Term → List (ℕ × Type) → Type → Term
      buildBody conArgLen `argLen argTypes resCtx =
        -- congₙ n con ...
        `congₙ `argLen (con₀ conName) (map buildArg argTypes)
        where
          open import Function.Nary.NonDependent using (congₙ)
          `congₙ : Term → Term → List (Arg Term) → Term
          `congₙ n f xs = def (quote congₙ) (vArg n ∷ vArg f ∷ xs)
          `refl : Term
          `refl = con₀ (quote refl)
          buildArg : (ℕ × Type) → Arg Term
          buildArg (ix , t) = vArg $
            if inheritsScope (ix + 1) resCtx tmName (vArg t)
            then inheritTerm conArgLen ix funName
            else `refl

buildApplyCong : Type → Term → Name → Term → TC ⊤
buildApplyCong `Typ `ts tmName acHole = do
  acName ← freshName "acGenerated"
  inferType acHole >>= declareDef (vArg acName)

  varName ← normalise `ts >>= getVarNameFromTs
  conNames ← getConstructors tmName
  clauses ← forA conNames $ LA.buildClause `Typ tmName varName acName staticTel
                                           varBody inheritTerm 5 0
  defineFun acName clauses
  unify acHole (def₀ acName)
  where
    open Quoted `Typ
    `CongAppArgs = def₂ (quote CongAppArgs) `Typ
    `Eq          = def₄ (quote Lemmas.Eq) `Typ
    `cong        = def₂ (quote cong)
    `embed       = def₁ (quote CongAppArgs.embed)
    `extCongN    = def₂ (quote CongAppArgs.extCongN)

    varBody : ℕ → Term
    varBody argLen = `cong (`embed (var₀ (argLen + 6)))
                           (var₁ (argLen + 1) (var₀ 0))

    inheritTerm : ℕ → ℕ → Name → Term
    inheritTerm argLen ix funName =
      def₃ funName `ca (`extCongN `ca `m₁≗m₂) (var₀ ix)
      where `ca    = weaken argLen (var₀ 6)
            `m₁≗m₂ = weaken argLen (var₀ 1)

    staticTel : Telescope
    staticTel = ("Dr"    , hArg `Deriv)
              ∷ ("e"     , hArg (`Embed (var₀ 0) (def₀ tmName)))
              ∷ ("ca"    , vArg (`CongAppArgs (var₀ 0)))
              ∷ ("Γ"     , hArg `Context)
              ∷ ("Δ"     , hArg `Context)
              ∷ ("m₁"    , hArg (`Map (var₀ 4) (var₀ 1) (var₀ 0)))
              ∷ ("m₂"    , hArg (`Map (var₀ 5) (var₀ 2) (var₀ 1)))
              ∷ ("m₁≗m₂" , vArg (`Eq (var₀ 6) (var₀ 1) (var₀ 0)))
              ∷ ("T"     , hArg `Typ)
              ∷ []

deriveTSCong' : ∀ {Typ} {Tm} {ts : TermSubst Typ Tm}
              → Term → TC ⊤
deriveTSCong' {Typ} {Tm} {ts} tscHole = do
  `Typ ← quoteTC Typ
  `Tm ← quoteTC Tm
  `ts ← quoteTC ts
  checkType tscHole $ def (quote TermSubstCong) $ `Typ ⟨∷⟩ `Tm ⟅∷⟆ `ts ⟨∷⟩ []
  (def₀ tmName) ← normalise `Tm
    where _ → typeErrorS "Couldn't infer Tm to a be concrete data type."

  applyCongHole ← newMeta!

  tscCon ← recordConstructor $ (quote TermSubstCong)
  unify tscHole $ con₁ tscCon applyCongHole
  buildApplyCong `Typ `ts tmName applyCongHole

  return tt

macro deriveTSCong = deriveTSCong'

buildApplyId : Type → Term → Name → Term → TC ⊤
buildApplyId `Typ `ts tmName aiHole = do
  aiName ← freshName "aiGenerated"
  inferType aiHole >>= declareDef (vArg aiName)

  varName ← normalise `ts >>= getVarNameFromTs

  conNames ← getConstructors tmName
  clauses ← forA conNames $ LA.buildClause `Typ tmName varName aiName staticTel
                                           varBody inheritTerm 1 0

  defineFun aiName clauses
  unify aiHole (def₀ aiName)

  where
    open Quoted `Typ
    `IdAppArgs = def₃ (quote IdAppArgs) `Typ
    `Eq        = def₄ (quote Lemmas.Eq) `Typ
    `trans     = def₂ (quote trans)
    `apply     = def₂ (quote TermSubst.apply)
    `e+id=var  = def₂ (quote IdAppArgs.e+id=var)
    `appExtCong = def (quote IdAppArgs.appExtCong)

    -- e+id=var ia x
    varBody : ℕ → Term
    varBody argLen = `e+id=var (var₀ (argLen + 2)) (var₀ 0)

    inheritTerm : ℕ → ℕ → Name → Term
    inheritTerm argLen ix funName =
      `trans
        -- appExtCong ia Γ tₙ
        (`appExtCong $ var₀ (argLen + 2) ⟨∷⟩ var₀ (argLen + 1) ⟨∷⟩ var₀ ix ⟨∷⟩ [])
        -- applyId ia tₙ
        (def₂ funName (var₀ (argLen + 2)) (var₀ ix))

    staticTel : Telescope
    staticTel = ("Dr"         , hArg `Deriv)
              ∷ ("e"          , hArg (`Embed (var₀ 0) (def₀ tmName)))
              ∷ ("ia"         , vArg (`IdAppArgs `ts (var₀ 0)))
              ∷ ("Γ"          , hArg `Context)
              ∷ ("T"          , hArg `Typ)
              ∷ []

deriveTSId' : ∀ {Typ} {Tm} {ts : TermSubst Typ Tm}
            → Term → TC ⊤
deriveTSId' {Typ} {Tm} {ts} tsiHole = do
  `Typ ← quoteTC Typ
  `Tm ← quoteTC Tm
  `ts ← quoteTC ts
  checkType tsiHole $ def (quote TermSubstId) $ `Typ ⟨∷⟩ `Tm ⟅∷⟆ `ts ⟨∷⟩ []

  (def₀ tmName) ← normalise `Tm

    where _ → typeErrorS "Couldn't infer Tm to a be concrete data type."

  applyIdHole ← newMeta!
  tscHole ← newMeta!
  tsiCon ← recordConstructor $ (quote TermSubstId)
  unify tsiHole $ con₃ tsiCon tscHole applyIdHole (con₀ (quote refl))

  deriveTSCong' {ts = ts} tscHole

  buildApplyId `Typ `ts tmName applyIdHole

macro deriveTSId = deriveTSId'
