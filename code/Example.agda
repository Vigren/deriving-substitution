module Example where
open import Data.List
open import Data.Nat hiding (_+_)

data Type : Set where
  Nat : Type
  _⇒_ : Type → Type → Type
  _+_ : Type → Type → Type

open import Substitution (Type)
open Variables

infix 4 _⊢_
infixr 6 _⇒_
infixl 7 _+_

data _⊢_ (Γ : Context) : Type → Set where
  var : (x : Γ ∋ A) → Γ ⊢ A
  nat : ℕ → (Γ ⊢ Nat)
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

    sub : ∀ {Γ Δ} → Map Dr Γ Δ → ∀ {A} → Γ ⊢ A → Δ ⊢ A
    sub m (var x)                = embed (m x)
    sub m (nat x)                = nat x
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

module LemmasManual where
  open Manual
  open import Lemmas (Type)
  open TermSubst manTs hiding (var)
  open import Function.Nary.NonDependent using (congₙ)
  open import Data.List.Relation.Unary.Any using (here ; there)
  open import Relation.Binary.PropositionalEquality hiding (subst)
  open import Function as Fun hiding (id)

  module _ {Dr : Deriv} (ec : EmbedCong Dr _⊢_) where
    open EmbedCong ec
    applyCong : ∀ {Γ Δ : Context} {m₁ m₂ : Map Dr Γ Δ}
              → Eq Dr m₁ m₂ → ∀ {A} → apply e m₁ {A} ≗ apply e m₂
    applyCong eq (var x)     = cong embed (eq x)
    applyCong eq (nat x)     = cong nat refl
    applyCong eq (app t t₁)  = cong₂ app (applyCong eq t)
                                         (applyCong eq t₁)
    applyCong eq (abs t)     = cong abs (applyCong (extCong eq) t)
    applyCong eq (left t)    = cong left (applyCong eq t)
    applyCong eq (right t)   = cong right (applyCong eq t)
    applyCong eq (case t l→ t₁ r→ t₂) =
      congₙ 3 case_l→_r→_
        (applyCong eq t)
        (applyCong (extCong eq)  t₁)
        (applyCong (extCong eq)  t₂)

  tsc : TermSubstCong _⊢_
  tsc = record { ts = manTs ; applyCong = applyCong }

  module _ {Dr : Deriv} (ei : EmbedId Dr _⊢_) where
    open EmbedId ei

    module _ (applyCong : ∀ {Γ Δ} {m₁ m₂ : Map Dr Γ Δ} → Eq Dr m₁ m₂
                        → ∀ {A} → apply e m₁ {A} ≗ apply e m₂ )
             (varCase : ∀ {Γ A} → apply e {Γ} id {A} ∘ var ≗ Fun.id ∘ var) where

      applyId : ∀ {Γ A} → apply e {Γ} id {A} ≗ Fun.id
      applyId (var x)    = varCase x
      applyId (nat x)    = cong nat refl
      applyId (app t t₁) = cong₂ app (applyId t) (applyId t₁)
      applyId (abs t)    = cong abs (trans (applyCong extId t)
                                           (applyId t))
      applyId (left t)   = cong left (applyId t)
      applyId (right t)  = cong right (applyId t)
      applyId (case t l→ t₁ r→ t₂) = congₙ 3 case_l→_r→_
        (applyId t)
        (trans (applyCong extId t₁) (applyId t₁))
        (trans (applyCong extId t₂) (applyId t₂))

  tsi : TermSubstId _⊢_
  tsi = record { tsCong   = tsc
               ; applyId  = applyId
               ; applyVar = refl
               }

module LemmasGenerated where
  open import Lemmas (Type)
  open import Tactic
  tsc : TermSubstCong _⊢_
  tsc = deriveTSCong
