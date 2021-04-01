module Tests where
open import Prelude hiding (_+_ ; abs)

infixr 6 _⇒_
infixl 7 _+_

data Type : Set where
  _⇒_ : Type → Type → Type
  _+_ : Type → Type → Type

open import Tactic (Type)
open import Substitution (Type)

module Doub where
  data _Doub_ (Γ : Context) : Type → Set where
    var : (x : Γ ∋ A) → Γ Doub A
    app : (f : Γ Doub (A ⇒ B)) (x : Γ Doub A) → Γ Doub B
    abs : (b : (A ∷ A ∷ Γ) Doub B) → (Γ Doub (A ⇒ B))

  ts : TermSubst (_Doub_)
  ts = deriveSubst
