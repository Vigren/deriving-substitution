module Tools where

open import Prelude
open import Prelude.Variables
open import Builtin.Reflection
open import Tactic.Reflection

typeErrorT : Term → TC A
typeErrorT = typeError ∘ [_] ∘ termErr

inContextTel : ∀ {a} {A : Set a} → Telescope → TC A → TC A
inContextTel tel = inContext (reverse (map snd tel))

-- a₀, a₁, a₂  →  (2, a₀), (1, a₁), (0, a₂)
reverseCount : List A → List (Nat × A)
reverseCount as = zip (reverse $ from 0 for length as) as
