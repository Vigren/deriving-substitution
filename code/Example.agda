module Example where
open import Data.List

data Type : Set where
  _⇒_ : Type → Type → Type
  _+_ : Type → Type → Type

open import Substitution (Type)
open Variables

infix 4 _⊢_
infixr 6 _⇒_
infixl 7 _+_

data _⊢_ (Γ : Context) : Type → Set where
  var : (x : Γ ∋ A) → Γ ⊢ A
  app : (f : Γ ⊢ A ⇒ B) (x : Γ ⊢ A) → Γ ⊢ B
  abs : (b : A ∷ Γ ⊢ B) → (Γ ⊢ A ⇒ B)
  left : (l : Γ ⊢ A) → (Γ ⊢ A + B)
  right : (r : Γ ⊢ B) → (Γ ⊢ A + B)
  case_l→_r→_
    : (l+r : Γ ⊢ A + B)
    → (lb : A ∷ Γ ⊢ C) (rb : B ∷ Γ ⊢ C)
    → Γ ⊢ C

module Manual where
  module _ {Dr : Deriv} (l : Embed Dr _⊢_) where
    open Embed l

    sub : ∀ {A Γ Δ} → Map Dr Γ Δ → Γ ⊢ A → Δ ⊢ A
    sub m (var x)                = embed (m x)
    sub m (app f x)              = app (sub m f) (sub m x)
    sub m (abs b)                = abs (sub (m ↑) b)
    sub m (left l)               = left (sub m l)
    sub m (right r)              = right (sub m r)
    sub m (case l+r l→ lb r→ rb) = case (sub m l+r)
                                  l→ (sub (m ↑) lb)
                                  r→ sub (m ↑) rb

  manTs : TermSubst _⊢_
  manTs = record { var = var ; apply = sub }

module Generated where
  open import Tactic using (deriveSubst)
  genTs : TermSubst (_⊢_)
  genTs = deriveSubst
