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
  `Lift      = def₃ (quote Lift) `Typ
  `Sub       = def₄ (quote Sub) `Typ
  `extend    = def₂ (quote Lift.extend)
  `lift      = def₂ (quote Lift.lift)

  -- Gets the first suitable var constructor.
  findVar : Term → List Name → TC Name
  findVar varHole conNames = do
    choice $ flip map conNames $ λ cn → catchTC
      (unify varHole (con₀ cn) >> return cn)
      (typeErrorS "No suitable var constructor found.")

  -- Given a vector of constructor arguments and index of the context variable
  -- in result types, returns telescope with whether arguments are recursive
  -- and how many variables they bind (that is, one for each cons).
  analyseCon : {ix : Nat} → Vec (String × Arg Type) ix
                          → Term → Name
                          → (Vec (String × Arg Type × Maybe Nat) ix)
  analyseCon {.zero} [] _ _ = []
  analyseCon ix@{suc _} ((x , tArg@(arg _ t)) ∷ tArgs) resCtxVar tmName =
    (x , tArg , recLevel t) ∷ analyseCon tArgs resCtxVar tmName
    where
      recLevel' : Type → Maybe Nat
      recLevel' typ =
        ifYes (weaken ix typ == resCtxVar)
        then return 0
        else case typ of λ
            { (con (quote List._∷_) (hArg _ ∷ hArg _ ∷ vArg _ ∷ vArg ctxs ∷ []))
                    → suc <$> recLevel' ctxs
            ; _    → nothing
            }

      -- | Argument is maybe recursive and needs n weakenings.
      recLevel : Type → Maybe Nat
      recLevel (def₂ dName ctxs _ ) =
        ifYes tmName == dName
        then recLevel' ctxs
        else nothing
      recLevel _ = nothing


  buildVarBody : {n : Nat} → Vec (String × Arg Type × Maybe Nat) n
               → Term
  buildVarBody {n = argLen } _ =
    `lift (var₀ (argLen + 4)) (var₁ (argLen + 0) (var₀ 0))

  buildBody : {n : Nat} → Name → Name
                  → Vec (String × Arg Type × Maybe Nat) n
                  → Term
  buildBody {n = argLen} applyName conName conTelRec =
    con conName $ vecToList $ mapIx
          (λ ix (_ , at , r) → buildConArg ix at r)
          conTelRec
    where
      `L `s : Term
      `L = weaken argLen (var₀ 4)
      `s = weaken argLen (var₀ 0)
      nth : Nat → Term
      nth ix = var₀ ix
      nExtended : Nat → Term
      nExtended 0       = `s
      nExtended (suc n) = `extend `L (nExtended n)
      -- TODO: hArg ↦ unknown is maybe a problem? Γ, A could be visible
      -- Makes the ix:th-argument for the constructor in the clause body.
      buildConArg : Nat → Arg Type → Maybe Nat → Arg Term
      buildConArg ix (vArg _) nothing  = vArg $ (nth ix)
      buildConArg ix (vArg _) (just b) =
        vArg $ def₃ applyName `L (nExtended b) (nth ix)
      buildConArg _  (arg ai _) _      = arg ai unknown

  buildClause : Name → Name → Name → Name → TC Clause
  buildClause tmName varName applyName conName = do
    let staticPartTel : Telescope
        staticPartTel =
          ("Tm" , hArg (`Deriv))
          ∷ ("L" , vArg (`Lift (var₀ 0) (def₀ tmName)))
          ∷ ("T" , (hArg `Typ))
          ∷ ("Γ" , (hArg `Context))
          ∷ ("Δ" , (hArg `Context))
          ∷ ("s" , vArg (`Sub (var₀ 4) (var₀ 1) (var₀ 0)))
          ∷ []

    #params ← conParams conName
    conTyp ← inContextTel staticPartTel $
      let unPi : Type → TC Type
          unPi = λ { (pi _ (abs _ rs)) → return rs
                    ; _ → typeErrorS "Panic: Parameter but no top pi type."
                    }
      in case #params of λ
        -- No parameters, no need to redirect anything
        { 0 → normalise =<< getType conName
        -- Context is parameter, redirect to apply functions.
        ; 1 → weaken 2 <$> (unPi =<< normalise =<< getType conName)
        -- Both context and type is parameter, redirect to apply functions.
        ; 2 →
            weaken 3 <$> (unPi =<<
            weaken 2 <$> (unPi =<< normalise =<< getType conName))

        ; n → typeErrorS "Panic: Too many params"
        }

    conTel , (def₂ _ resCtx resTyp) ← return $ telView conTyp
      where _ → typeErrorS $
                  "Constructor doesn't produce Tm"
                  <> " or result type context is not a variable."

    let conTelRec : Vec (String × Arg Type × Maybe Nat) (length conTel)
        conTelRec = analyseCon (listToVec conTel) resCtx tmName

    let matchTel : Telescope
        matchTel = staticPartTel ++ conTel

    let pat : List (Arg Pattern)
        pat = weaken (length conTel) (telePat staticPartTel)
              ++ [ vArg (con conName (telePat conTel)) ]

    -- Assuming just apply args + constructor args are in scope
    let body : Term
        body = ifYes conName == varName
               then buildVarBody conTelRec
               else buildBody applyName conName conTelRec

    return (clause matchTel pat body)


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
      (def₂ tmSubName `Typ (def₀ tmName)) ← normalise =<< inferType tsHole
        where _ → typeErrorS ""

      tsCon ← recordConstructor $ tmSubName
      unify tsHole $ con₂ tsCon varHole applyHole

      varName ← getConstructors tmName >>= findVar `Typ varHole

      getConstructors tmName >>= buildApply `Typ applyHole tmName varName

      return tt
