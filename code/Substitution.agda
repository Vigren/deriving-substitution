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

Sub : Deriv → Context → Context → Set
Sub Tm Γ Δ = ∀ {A} → Γ ∋ A → Tm Δ A

variable
  A B C : Type
  Γ Δ Κ : Context

record Simple (Tm : Deriv) : Set where
  field
    var    : Γ ∋ A → Tm Γ A
    weaken : Tm Γ A → Tm (B ∷ Γ) A

  infixl  10 _↑

  -- Lifts / extends a substitution so a new topmost variable,
  -- of type `A`, is mapped to a new topmost variable.
  extend _↑ : Sub Tm Γ Δ → Sub Tm (A ∷ Γ) (A ∷ Δ)
  extend _ (here refl) = var (here refl)
  extend s (there i)   = weaken (s i)
  _↑ = extend


  -- The identity (unit?) substitution
  id : Sub Tm Γ Γ
  id = var

  wk : Sub Tm Γ (B ∷ Γ)
  wk {Γ = _ ∷ _} = weaken ∘ id

record Application (Tm₁ Tm₂ : Deriv) : Set where
  field
    app : Sub Tm₂ Γ Δ → Tm₁ Γ A → Tm₁ Δ A

  _⊙_ : Sub Tm₂ Δ Κ → Sub Tm₁ Γ Δ → Sub Tm₁ Γ Κ
  Κ←Δ ⊙ Δ←Γ = app Κ←Δ ∘ Δ←Γ


record Subst (Tm : Deriv) : Set where
  field
    simple : Simple Tm
    application : Application Tm Tm

  open Simple      simple      public
  open Application application public


record Embed (Tm₁ Tm₂ : Deriv) : Set where
  field
    simple : Simple Tm₁
    embed : Tm₁ Γ A → Tm₂ Γ A

  open Simple simple public

module VarSubst where
  subst : Subst _∋_
  subst = record
    { simple = record
      { var    = F.id
      ; weaken = there
      }
    ; application = record { app = λ f x → f x }}

  open Subst subst public

record TermSubst (Tm : Deriv) : Set₁ where
  field
    var : Γ ∋ A → Tm Γ A
    apply : ∀ {Tm' : Deriv} → Embed Tm' Tm
          → ∀ {A Γ Δ} → Sub Tm' Γ Δ
          → Tm Γ A
          → Tm Δ A

  module Embedded {Tm' : Deriv} (e : Embed Tm' Tm) where
    application : Application Tm Tm'
    application = record { app = apply e }

  varEmbed : Embed _∋_ Tm
  varEmbed = record { simple = VarSubst.simple
                    ; embed  = var
                    }

  rename : Sub _∋_ Γ Δ → Tm Γ A → Tm Δ A
  rename = apply varEmbed

  simple : Simple Tm
  simple = record { var    = var
                  ; weaken = rename VarSubst.wk
                  }

  idEmbed : Embed Tm Tm
  idEmbed = record { simple = simple
                   ; embed = F.id
                   }

  subst : Subst Tm
  subst = record { simple      = simple
                 ; application = Embedded.application idEmbed
                 }
