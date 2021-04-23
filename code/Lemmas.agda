module Lemmas (Type : Set) where

open import Substitution (Type)
open Variables
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

  id≡var : id {Γ} {A = A} ≡ var
  id≡var = refl

  ↑-cong : s₁ ≗ₛ s₂
         → extend {A = A} s₁ ≗ₛ extend s₂
  ↑-cong _ (here refl)   = refl
  ↑-cong s₁≗s₂ (there i) = cong weaken (s₁≗s₂ i)

record Lemmas-weaken-var (Tm : Deriv) : Set where
  field lemmas-simple : LemmasSimple Tm

  open LemmasSimple lemmas-simple
  open Simple simple

  field weaken-var : weaken {Γ} {A} {B} ∘ var ≗ var ∘ there

  -- A lifted identity substitution is
  -- the identity substitution of one more thing.
  extend-id : extend {Γ} id {A} ≗ id {A ∷ Γ}
  extend-id (here refl) = refl
  extend-id (there i) = weaken-var i

  -- Possible: wk ≗ var ∘ there

  -- Possible: (s₁ ≗ₛ var ∘ there) → (s₁ ↑) ≗ var ∘ there
