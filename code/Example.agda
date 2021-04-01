module Example where
open import Data.List
open import Data.List.Membership.Propositional

data Type : Set where
  _⇒_ : Type → Type → Type
  _+_ : Type → Type → Type

open import Substitution (Type)

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

module Manual {Tm : Deriv} (l : Lift Tm _⊢_) where
  open Lift l hiding (var)

  sub : ∀ {A Γ Δ } → Sub Tm Γ Δ → Γ ⊢ A → Δ ⊢ A
  sub s (var x)                = lift (s x)
  sub s (app f x)              = app (sub s f) (sub s x)
  sub s (abs b)                = abs (sub (s ↑) b)
  sub s (left l)               = left (sub s l)
  sub s (right r)              = right (sub s r)
  sub s (case l+r l→ lb r→ rb) = case (sub s l+r)
                                 l→ (sub (s ↑) lb)
                                 r→ sub (s ↑) rb

manTs : TermSubst _⊢_
manTs = record { var = var ; apply = Manual.sub }

module Generated where
  open import Tactic
  genTs : TermSubst (_⊢_)
  genTs = deriveSubst
