module Tools where

open import Prelude
open import Prelude.Variables
open import Builtin.Reflection
open import Tactic.Reflection

typeErrorT : Term → TC A
typeErrorT = typeError ∘ [_] ∘ termErr

mapIx : {n : Nat} → (Nat → A → B) → Vec A n → Vec B n
mapIx {n = .zero} _ [] = []
mapIx {n = (suc m)} f (x ∷ v) = f m x ∷ mapIx f v

inContextTel : ∀ {a} {A : Set a} → Telescope → TC A → TC A
inContextTel tel = inContext (reverse (map snd tel))
