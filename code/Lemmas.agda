module Lemmas (Type : Set) where

open import Substitution (Type)
import Function as F
open F using (_$_ ; _∘_)
open import Data.List
open import Data.List.Membership.Propositional
open import Data.List.Membership.Setoid using (_∈_)
open import Data.List.Relation.Unary.Any
  using (here ; there ; Any)
open import Relation.Binary.PropositionalEquality
            hiding (subst)

open ≡-Reasoning

record LemmasSimple (Tm : Deriv) : Set where
  field simple : Simple Tm

  open Simple simple

  variable
    s₁ s₂ : Sub Tm Γ Δ

  infix 4 _≗ₛ_

  -- Pointwise equality on Tm-substitutions
  _≗ₛ_ : (s₁ s₂ : Sub Tm Γ Δ) → Set
  s₁ ≗ₛ s₂ = ∀ {A} → s₁ {A} ≗ s₂ {A}

  -- A lifted identity substitution is
  -- the identity substitution of one more thing.
  ↑-id : (id {Γ} ↑) {A} ≡ id {A ∷ Γ}
  ↑-id = refl

  ↑-cong : s₁ ≗ₛ s₂
         → extend {A = A} s₁ ≗ₛ extend s₂
  ↑-cong _ (here refl)   = refl
  ↑-cong s₁≗s₂ (there i) = cong weaken (s₁≗s₂ i)

record Lemmas-weaken-var (Tm : Deriv) : Set where
  field lemmas-simple : LemmasSimple Tm

  open LemmasSimple lemmas-simple
  open Simple simple

  field weaken-var : weaken {Γ} {A} {B} ∘ var ≗ var ∘ there

  id≗var : id {Γ} ≗ₛ var
  id≗var (here refl) = refl
  id≗var (there i) = trans (cong weaken $ id≗var i) (weaken-var i)

  -- Possible: wk ≗ var ∘ there

  -- Possible: (s₁ ≗ₛ var ∘ there) → (s₁ ↑) ≗ var ∘ there
