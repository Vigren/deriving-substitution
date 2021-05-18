{-# OPTIONS --allow-unsolved-metas #-}

module Tactic where

open import Prelude
open import Container.Traversable
open import Tactic.Reflection

open import Tools
open import Substitution
open import Lemmas

-- TODO: Could instead check if its unifiable with ∀ {Κ}. Κ ++ resCtx
inheritsScope : Nat → Arg Type → Term → Name → Bool
inheritsScope ix (arg _ (def₂ dName ctxs _)) resCtx tmName =
  dName ==? tmName && isWeakened ctxs
  where
    isWeakened : Type → Bool
    isWeakened typ =
      if weaken (ix + 1) typ ==? resCtx
      then true
      else case typ of λ
          { (con (quote List._∷_) (hArg _ ∷ hArg _ ∷ vArg _ ∷ vArg ctxs ∷ []))
                 → isWeakened ctxs
          ; _    → false
          }
inheritsScope _ _ _ _ = false

-- Gets the first suitable var constructor.
findVar : Term → List Name → TC Name
findVar varHole conNames = do
  choice $ flip map conNames $ λ cn → catchTC
    (unify varHole (con₀ cn) >> return cn)
    (typeErrorS "No suitable var constructor found.")

-- Substitutes references to parameters in a constructor type
-- for some variable in a telescope.
redirectParams : Name → Telescope → Nat → Nat → TC Type
redirectParams conName staticTel contextIndex typeIndex = do
  #params ← conParams conName
  inContextTel staticTel $
    let unPi : Type → TC Type
        unPi = λ { (pi _ (abs _ rs)) → return rs
                  ; _ → typeErrorS "Panic: Parameter but no top pi type."
                  }
    in do
      t ← normalise =<< getType conName
      case #params of λ
        -- No parameters, no need to redirect anything
        { 0 → return t
        -- Context is parameter, redirect to static Γ.
        ; 1 → substTerm [ safe (var₀ contextIndex) tt ] <$> unPi t
        -- Both context and type is parameter, redirect to static Γ, T
        ; 2 → substTerm ( safe (var₀ typeIndex) tt
                        ∷ (safe (var₀ contextIndex) tt)
                        ∷ []) <$> (unPi =<< unPi t)

        ; n → typeErrorS "Panic: Too many params"
        }

module TS (`Typ : Type) (tmName : Name) (varName : Name) where
  `Context   = def₁ (quote Context) `Typ
  `Deriv     = def₁ (quote Deriv) `Typ
  `TermSubst = def₃ (quote TermSubst) `Typ
  `Embed     = def₃ (quote Embed) `Typ
  `Map       = def₄ (quote Map) `Typ
  `extendN   = def₂ (quote Embed.extendN)
  `embed     = def₂ (quote Embed.embed)

  -- The initial, static part of the apply telescope
  staticPartTel : Telescope
  staticPartTel =
      ("Dr" , hArg (`Deriv))
    ∷ ("e" , vArg (`Embed (var₀ 0) (def₀ tmName)))
    ∷ ("Γ" , hArg `Context)
    ∷ ("Δ" , hArg `Context)
    ∷ ("m" , vArg (`Map (var₀ 3) (var₀ 1) (var₀ 0)))
    ∷ ("T" , hArg `Typ)
    ∷ []

  buildVarBody : Nat → Term
  buildVarBody argLen =
    -- Embed.embed e (m x)
    `embed (var₀ (argLen + 4)) (var₁ (argLen + 1) (var₀ 0))

  buildBody : Name → Name
            → List (Nat × Arg Type) → Type → Term
  buildBody applyName conName argTypes resCtx =
    con conName $ map buildConArg argTypes
    where
      argLen = length argTypes
      `e `m : Term
      `e = weaken argLen (var₀ 4)
      `m = weaken argLen (var₀ 1)
      -- TODO: hArg ↦ unknown is maybe a problem? Γ, A could be visible
      -- Makes the ix:th constructor in the clause body.
      buildConArg : (Nat × Arg Type) → Arg Term
      buildConArg (ix , vArg t) = vArg $
        if inheritsScope ix (vArg t) resCtx tmName
        then def₃ applyName `e (`extendN `e `m) (var₀ ix)
        else var₀ ix
      buildConArg (_ , arg ai _) = arg ai unknown

  buildClause : Name → Name → TC Clause
  buildClause applyName conName = do
    -- If a data type argument is a parameter,
    -- then we need to "redirect" the constructor argument
    -- to the corresponding one in the apply function.
    conTyp ← redirectParams conName staticPartTel 3 0

    -- conTel is the dynamic part of the telescope,
    -- which we get by decomposing the Tm constructor.
    conTel , (def₂ _ resCtx resTyp) ← return $ telView conTyp
      where _ → typeErrorS "Constructor doesn't produce Tm"

    let tel : Telescope
        tel = staticPartTel ++ conTel

    let pat : List (Arg Pattern)
        pat = weaken (length conTel) (telePat staticPartTel)
              ++ [ vArg (con conName (telePat conTel)) ]

    -- Constructor argument types and their de Bruijn indices in tel / conTel.
    -- Assumes all constructor args correspond to exactly one variable in pat.
    let argTypes : List (Nat × Arg Type)
        argTypes = reverseCount (map snd conTel)

    let body : Term
        body = if conName ==? varName
               then buildVarBody (length conTel)
               else buildBody applyName conName argTypes resCtx

    return (clause tel pat body)

  buildApply : Term → List Name → TC ⊤
  buildApply applyHole conNames = do
    applyName ← freshName "applyGenerated"
    inferType applyHole >>= declareDef (vArg applyName)

    -- TODO: Prepend constructor name to error stack?
    clauses ← mapM (buildClause applyName) conNames

    defineFun applyName clauses
    unify applyHole (def₀ applyName)


deriveSubst' : Term → TC Name
deriveSubst' tsHole = do
  varHole ← newMeta!
  applyHole ← newMeta!
  (def₂ (quote TermSubst) `Typ (def₀ tmName)) ← normalise =<< inferType tsHole
    where _ → typeErrorS ""

  tsCon ← recordConstructor $ (quote TermSubst)
  unify tsHole $ con₂ tsCon varHole applyHole

  conNames ← getConstructors tmName
  varName ← findVar varHole conNames
  TS.buildApply `Typ tmName varName applyHole conNames

  return varName

macro deriveSubst = (tt <$_) ∘ deriveSubst'

module TSC (`Typ : Type) (tmName : Name) (varName : Name) where
  open import Function.Nary.NonDependent using (congₙ)
  open TS `Typ tmName varName using (`Context ; `Deriv ; `Map)
  `EmbedCong = def₃ (quote EmbedCong) `Typ
  `Eq        = def₄ (quote Lemmas.Eq) `Typ
  `cong      = def₂ (quote cong)
  `embed     = def₁ (quote EmbedCong.embed)
  `extCongN  = def₂ (quote EmbedCong.extCongN)
  `refl : Term
  `refl = con₀ (quote refl)
  `congₙ : Term → Term → List (Arg Term) → Term
  `congₙ n f xs = def (quote congₙ) (vArg n ∷ vArg f ∷ xs)

  staticPartTel : Telescope
  staticPartTel =
       ("Dr"   , hArg `Deriv)
    ∷ ("ec"    , vArg (`EmbedCong (var₀ 0) (def₀ tmName)))
    ∷ ("Γ"     , hArg `Context)
    ∷ ("Δ"     , hArg `Context)
    ∷ ("m₁"    , hArg (`Map (var₀ 3) (var₀ 1) (var₀ 0)))
    ∷ ("m₂"    , hArg (`Map (var₀ 4) (var₀ 2) (var₀ 1)))
    ∷ ("m₁≗m₂" , vArg (`Eq (var₀ 5) (var₀ 1) (var₀ 0)))
    ∷ ("T"     , hArg `Typ)
    ∷ []

  buildVarBody : Nat → Term
  buildVarBody argLen =
    -- cong (EmbedCong.embed ec) (m₁≗m₂ x)
    `cong (`embed (var₀ (argLen + 6))) (var₁ (argLen + 1) (var₀ 0))

  -- TODO: Congₙ only supports explicit arguments.
  buildBody : Name → Name → Nat → Term → List (Nat × Type) → Type → Term
  buildBody acName conName conArgLen `argLen argTypes resCtx =
    -- congₙ n con ...
    `congₙ `argLen (con₀ conName) (map buildArg argTypes)
    where
      `ec `m₁≗m₂ : Term
      `ec    = weaken conArgLen (var₀ 6)
      `m₁≗m₂ = weaken conArgLen (var₀ 1)
      buildArg : (Nat × Type) → Arg Term
      buildArg (ix , t) = vArg $
        if inheritsScope ix (vArg t) resCtx tmName
        -- applyCong ec (extCongN m₁≗m₂) tᵢₓ
        then def₃ acName `ec (`extCongN `ec `m₁≗m₂) (var₀ ix)
        else `refl


  buildClause : Name → Name → TC Clause
  buildClause acName conName = do
    conTyp ← redirectParams conName staticPartTel 5 0

    conTel , (def₂ _ resCtx resTyp) ← return $ telView conTyp
      where _ → typeErrorS $ "Constructor doesn't produce Tm"

    let tel : Telescope
        tel = staticPartTel ++ conTel

    let pat : List (Arg Pattern)
        pat = weaken (length conTel) (telePat staticPartTel)
              ++ [ vArg (con conName (telePat conTel)) ]

    -- Pairs of visible constructor arguments and their de Bruijn indices
    let visibleArgTypes : List (Nat × Type)
        visibleArgTypes = map (second unArg)
                        ∘ filter (isVisible ∘ snd)
                        ∘ reverseCount
                        $ map snd conTel

    let conArgLen = length conTel
    `vArgLen ← quoteTC $ length visibleArgTypes

    -- Assuming just apply args + constructor args are in scope
    let body : Term
        body = if conName ==? varName
               then buildVarBody conArgLen
               else buildBody acName conName conArgLen
                              `vArgLen visibleArgTypes resCtx


    return (clause tel pat body)

  buildApplyCong : Term → TC ⊤
  buildApplyCong acHole = do
    acName ← freshName "acGenerated"
    inferType acHole >>= declareDef (vArg acName)

    conNames ← getConstructors tmName
    clauses ← mapM (buildClause acName) conNames

    defineFun acName clauses
    unify acHole (def₀ acName)


deriveTSCong' : Term → TC ⊤
deriveTSCong' tslHole = do
  (def₂ (quote TermSubstCong) `Typ (def₀ tmName)) ←
        normalise =<< inferType tslHole
    where _ → typeErrorS ""

  tsHole ← newMeta!
  applyCongHole ← newMeta!
  tsCon ← recordConstructor $ (quote TermSubstCong)
  unify tslHole $ con₂ tsCon tsHole applyCongHole

  varName ← deriveSubst' tsHole
  TSC.buildApplyCong `Typ tmName varName applyCongHole

macro deriveTSCong = deriveTSCong'
