module Tests where
open import Prelude hiding (_+_ ; abs)

infixr 6 _⇒_
infixl 7 _+_

data Type : Set where
  _⇒_ : Type → Type → Type
  _+_ : Type → Type → Type

open import Tactic
open import Substitution (Type)
open Variables

module Double where
  data Tm (Γ : Context) : Type → Set where
    var : Γ ∋ A → Tm Γ A
    app : Tm Γ (A ⇒ B) → Tm Γ A → Tm Γ B
    abs : Tm (A ∷ A ∷ Γ) B → Tm Γ (A ⇒ B)

  ts : TermSubst Tm
  ts = deriveSubst

module TwoParam where
  data Tm (Γ : Context) (A : Type) : Set where
    var : Γ ∋ A → Tm Γ A
    app : Tm Γ (B ⇒ A) → Tm Γ B → Tm Γ A

  ts : TermSubst Tm
  ts = deriveSubst
