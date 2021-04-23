module Substitution (Type : Set) where
open import Agda.Builtin.Equality
open import Data.List
open import Data.List.Membership.Propositional
open import Data.List.Relation.Unary.Any
  using (Any; here; there)
open import Function as F using (flip ; _∘_)

Context : Set
Context = List Type

_∋_ : Context → Type → Set
_∋_ = flip _∈_

Deriv : Set₁
Deriv = Context → Type → Set

-- Type preserving maps
Map : Deriv → Context → Context → Set
Map Tm Γ Δ = ∀ {A} → Γ ∋ A → Tm Δ A

module Variables where
  variable
    A B C : Type
    Γ Δ Κ : Context
open Variables

record Simple (Dr : Deriv) : Set where
  field
    var    : Γ ∋ A → Dr Γ A
    weaken : Dr Γ A → Dr (B ∷ Γ) A

  infixl  10 _↑

  -- Lifts / extends a derivation map so a new topmost variable
  -- is mapped to a new topmost variable, and the rest is weakened.
  extend _↑ : Map Dr Γ Δ → Map Dr (A ∷ Γ) (A ∷ Δ)
  extend _ (here refl) = var (here refl)
  extend s (there i)   = weaken (s i)
  _↑ = extend


  -- The identity map
  id : Map Dr Γ Γ
  id = var

  wk : Map Dr Γ (A ∷ Γ)
  wk {Γ = _ ∷ _} = weaken ∘ id

record Application (Dr₁ Dr₂ : Deriv) : Set where
  field
    app : Map Dr₂ Γ Δ → Dr₁ Γ A → Dr₁ Δ A

  _⊙_ : Map Dr₂ Δ Κ → Map Dr₁ Γ Δ → Map Dr₁ Γ Κ
  Κ←Δ ⊙ Δ←Γ = app Κ←Δ ∘ Δ←Γ


record Subst (Dr : Deriv) : Set where
  field
    simple : Simple Dr
    application : Application Dr Dr

  open Simple      simple      public
  open Application application public


record Embed (Dr₁ Dr₂ : Deriv) : Set where
  field
    simple : Simple Dr₁
    embed : Dr₁ Γ A → Dr₂ Γ A

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
    apply : ∀ {Dr : Deriv} → Embed Dr Tm
          → ∀ {A Γ Δ} → Map Dr Γ Δ
          → Tm Γ A
          → Tm Δ A

  varEmbed : Embed _∋_ Tm
  varEmbed = record { simple = VarSubst.simple
                    ; embed  = var
                    }

  rename : Map _∋_ Γ Δ → Tm Γ A → Tm Δ A
  rename = apply varEmbed

  simple : Simple Tm
  simple = record { var    = var
                  ; weaken = rename VarSubst.wk
                  }

  idEmbed : Embed Tm Tm
  idEmbed = record { simple = simple
                   ; embed = F.id
                   }

  tmSubst : Subst Tm
  tmSubst = record { simple      = simple
                   ; application = record { app = apply idEmbed }
                   }
