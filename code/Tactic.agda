{-# OPTIONS --allow-unsolved-metas #-}

module Tactic where

open import Prelude
open import Container.Traversable
open import Tactic.Reflection
open import Tactic.Deriving

open import Tools
open import Substitution

module _ (`Typ : Type) where
  `Context   = def₁ (quote Context) `Typ
  `Deriv     = def₁ (quote Deriv) `Typ
  `TermSubst = def₃ (quote TermSubst) `Typ
  `Embed     = def₃ (quote Embed) `Typ
  `Map       = def₄ (quote Map) `Typ
  `extendN   = def₂ (quote Embed.extendN)
  `embed     = def₂ (quote Embed.embed)

  -- Gets the first suitable var constructor.
  findVar : Term → List Name → TC Name
  findVar varHole conNames = do
    choice $ flip map conNames $ λ cn → catchTC
      (unify varHole (con₀ cn) >> return cn)
      (typeErrorS "No suitable var constructor found.")

  -- TODO: Could instead check if its unifiable with ∀ {Κ}. Κ ++ resCtx
  analyseArg : Nat → Arg Type → Term → Name → Bool
  analyseArg ix (arg _ (def₂ dName ctxs _)) resCtx tmName =
    dName ==? tmName && isWeakened ctxs
    where
      isWeakened : Type → Bool
      isWeakened typ =
        ifYes (weaken ix typ == resCtx)
        then true
        else case typ of λ
            { (con (quote List._∷_)
                   (hArg _ ∷ hArg _ ∷ vArg _ ∷ vArg ctxs ∷ []))
                   → isWeakened ctxs
            ; _    → false
            }
  analyseArg _ _ _ _ = false


  buildVarBody : {n : Nat} → Vec (Arg Type) n → Term
  buildVarBody {n = argLen } _ =
    `embed (var₀ (argLen + 4)) (var₁ (argLen + 1) (var₀ 0))

  buildBody : {n : Nat} → Name → Name
                  → Vec (Arg Type) n
                  → Type → Name → Term
  buildBody {n = argLen} applyName conName argTypes resCtx tmName =
    con conName $ vecToList $ mapIx buildConArg argTypes
    where
      `e `m : Term
      `e = weaken argLen (var₀ 4)
      `m = weaken argLen (var₀ 1)
      nth : Nat → Term
      nth ix = var₀ ix
      -- TODO: hArg ↦ unknown is maybe a problem? Γ, A could be visible
      -- Makes the ix:th constructor in the clause body.
      buildConArg : Nat → Arg Type → Arg Term
      buildConArg ix (vArg t) = vArg $
        if analyseArg ix (vArg t) resCtx tmName
        then nth ix
        else def₃ applyName `e (`extendN `e `m) (nth ix)
      buildConArg _  (arg ai _) = arg ai unknown

  buildClause : Name → Name → Name → Name → TC Clause
  buildClause tmName varName applyName conName = do
    -- The initial, static part of the apply telescope
    let staticPartTel : Telescope
        staticPartTel =
          ("Dr" , hArg (`Deriv))
          ∷ ("e" , vArg (`Embed (var₀ 0) (def₀ tmName)))
          ∷ ("Γ" , (hArg `Context))
          ∷ ("Δ" , (hArg `Context))
          ∷ ("m" , vArg (`Map (var₀ 3) (var₀ 1) (var₀ 0)))
          ∷ ("T" , (hArg `Typ))
          ∷ []

    -- If a data type argument is a parameter,
    -- then we need to "redirect" the constructor argument
    -- to the corresponding one in the apply function.
    #params ← conParams conName
    conTyp ← inContextTel staticPartTel $
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
          ; 1 → substTerm [ safe (var₀ 3) tt ] <$> unPi t
          -- Both context and type is parameter, redirect to static Γ, T
          ; 2 → substTerm ( safe (var₀ 0) tt
                          ∷ (safe (var₀ 3) tt)
                          ∷ []) <$> (unPi =<< unPi t)

          ; n → typeErrorS "Panic: Too many params"
          }

    -- conTel is the dynamic part of the telescope,
    -- which we get by decomposing the Tm constructor.
    conTel , (def₂ _ resCtx resTyp) ← return $ telView conTyp
      where _ → typeErrorS $
                  "Constructor doesn't produce Tm"

    let tel : Telescope
        tel = staticPartTel ++ conTel

    let pat : List (Arg Pattern)
        pat = weaken (length conTel) (telePat staticPartTel)
              ++ [ vArg (con conName (telePat conTel)) ]

    -- Assuming just apply args + constructor args are in scope
    let body : Term
        body = let argTypes = listToVec (map snd conTel)
               in ifYes conName == varName
                  then buildVarBody argTypes
                  else buildBody applyName conName argTypes resCtx tmName

    return (clause tel pat body)


  buildApply : Term → Name → Name → List Name → TC ⊤
  buildApply applyHole tmName varName conNames = do
    applyName ← freshName "applyGenerated"
    inferType applyHole >>= declareDef (vArg applyName)

    -- TODO: Prepend constructor name to error stack?
    clauses ← mapM (buildClause tmName varName applyName)
                   conNames


    defineFun applyName clauses

    unify applyHole (def₀ applyName)

    return tt

macro
  deriveSubst : Term → TC ⊤
  deriveSubst tsHole = do
      varHole ← newMeta!
      applyHole ← newMeta!
      (def₂ (quote TermSubst) `Typ (def₀ tmName)) ←
            normalise =<< inferType tsHole
        where _ → typeErrorS ""

      tsCon ← recordConstructor $ (quote TermSubst)
      unify tsHole $ con₂ tsCon varHole applyHole

      conNames ← getConstructors tmName
      varName ← findVar `Typ varHole conNames
      buildApply `Typ applyHole tmName varName conNames

      return tt
