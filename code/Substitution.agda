module Substitution (Type : Set) where
open import Agda.Builtin.Equality
open import Data.List
open import Data.List.Membership.Propositional
open import Data.List.Relation.Unary.Any
  using (Any; here; there)
open import Function as F using (flip ; _∘_)

_∋_ : {A : Set} → List A → A → Set
_∋_ = flip _∈_

Context : Set
Context = List Type

Deriv : Set₁
Deriv = Context → Type → Set

variable
  A B C : Type
  Γ Δ Κ : Context

Sub : Deriv → Context → Context → Set
Sub Tm Γ Δ = ∀ {A} → A ∈ Γ → Tm Δ A

record Subst (Tm : Deriv) : Set where
  infixl 8  _/_
  infixl  10 _↑

  field
    var    : A ∈ Γ → Tm Γ A
    weaken : Tm Γ A → Tm (B ∷ Γ) A
    _/_    : Tm Γ A → Sub Tm Γ Δ → Tm Δ A

  -- Lifts / extends a substitution so a new topmost variable,
  -- of type `A`, is mapped to a new topmost variable.
  _↑ : Sub Tm Γ Δ → Sub Tm (A ∷ Γ) (A ∷ Δ)
  (_ ↑) (here refl) = var (here refl)
  (s ↑) (there i) = weaken (s i)

  -- The identity (unit?) substitution
  id : Sub Tm Γ Γ
  id = var

  wk : Sub Tm Γ (B ∷ Γ)
  wk {Γ = _ ∷ _} = weaken ∘ id ↑

  _⊙_ : Sub Tm Γ Δ → Sub Tm Δ Κ → Sub Tm Γ Κ
  Γ-Δ ⊙ Δ-Κ = λ i → var i / Γ-Δ / Δ-Κ

record Lift (Tm₁ Tm₂ : Deriv) : Set where
  field
    lift : Tm₁ Γ A → Tm₂ Γ A

module VarSubst where
  subst : Subst _∋_
  subst = record
    { var    = F.id
    ; weaken = there
    ; _/_    = λ i s → s i
    }

  open Subst subst public

record TermSubst (Tm : Deriv) : Set₁ where
  field
    var : Γ ∋ A → Tm Γ A
    app : ∀ {Tm' : Deriv} → Lift Tm' Tm
        → ∀ {Γ Δ} → Sub Tm' Γ Δ
        → Tm Γ A
        → Tm Δ A

  varLift : Lift _∋_ Tm
  varLift = record { lift = var }

  rename : Sub _∋_ Γ Δ → Tm Γ A → Tm Δ A
  rename = app varLift

  idLift : Lift Tm Tm
  idLift = record { lift = F.id }

  subst : Subst Tm
  subst = record
    { var    = var
    ; weaken = rename VarSubst.wk
    ; _/_    = flip (app idLift)
    }
