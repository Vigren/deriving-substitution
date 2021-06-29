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

    apply : ∀ {Γ Δ} → Map Dr Γ Δ → ∀ {A} → Γ ⊢ A → Δ ⊢ A
    apply m (var x)                = embed (m x)
    apply m (nat x)                = nat x
    apply m (app f x)              = app (apply m f) (apply m x)
    apply m (abs b)                = abs (apply (m ↑) b)
    apply m (left l)               = left (apply m l)
    apply m (right r)              = right (apply m r)
    apply m (case l+r l→ lb r→ rb) = case (apply m l+r)
                                  l→ (apply (m ↑) lb)
                                  r→ apply (m ↑) rb

  manTs : TermSubst _⊢_
  manTs = record { var = var ; apply = apply }

module Generated where
  open import Tactic using (deriveSubst)
  genTs : TermSubst (_⊢_)
  genTs = deriveSubst

module LemmasManual where
  open Manual
  open import Lemmas (Type)
  open TermSubst manTs hiding (var ; apply)
  open import Function.Nary.NonDependent using (congₙ)
  open import Data.List.Relation.Unary.Any using (here ; there)
  open import Relation.Binary.PropositionalEquality hiding (subst)
  open import Function as Fun hiding (id)

  module _ {Dr : Deriv} {e : Embed Dr _⊢_} (ca : CongAppArgs e) where
    open CongAppArgs ca

    applyCong : ∀ {m₁ m₂ : Map Dr Γ Δ} → Eq Dr m₁ m₂
              → ∀ {A} → apply e m₁ {A} ≗ apply e m₂
    applyCong eq (var x)     = cong embed (eq x)
    applyCong eq (nat x)     = cong nat refl
    applyCong eq (app t t₁)  = cong₂ app (applyCong eq t) (applyCong eq t₁)
    applyCong eq (abs t)     = cong abs (applyCong (extCong eq) t)
    applyCong eq (left t)    = cong left (applyCong eq t)
    applyCong eq (right t)   = cong right (applyCong eq t)
    applyCong eq (case t l→ t₁ r→ t₂) =
      congₙ 3 case_l→_r→_
        (applyCong eq t)
        (applyCong (extCong eq) t₁)
        (applyCong (extCong eq) t₂)

  tsc : TermSubstCong manTs
  tsc = record { applyCong = applyCong }

  module _ {Dr : Deriv} {e : Embed Dr _⊢_} (ia : IdAppArgs manTs e) where
    open IdAppArgs ia

    applyId : apply e {Γ} id {A} ≗ Fun.id
    applyId (var x)    = e+id=var x
    applyId (nat x)    = cong nat refl
    applyId (app t t₁) = cong₂ app (applyId t) (applyId t₁)
    applyId {Γ} (abs t) = cong abs (trans (appExtCong {Γ} t) (applyId t))
    applyId (left t)   = cong left (applyId t)
    applyId (right t)  = cong right (applyId t)
    applyId {Γ} (case t l→ t₁ r→ t₂) = congₙ 3 case_l→_r→_
      (applyId t)
      (trans (appExtCong {Γ} t₁) (applyId t₁))
      (trans (appExtCong {Γ} t₂) (applyId t₂))

  tsi : TermSubstId manTs
  tsi = record { tsCong   = tsc
               ; applyId  = applyId
               ; applyVar = refl
               }

module LemmasGenerated where
  open import Lemmas (Type)
  open import Tactic
  open Generated

  tsc : TermSubstCong genTs
  tsc = deriveTSCong
