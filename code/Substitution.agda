module Substitution (Type : Set) where
open import Agda.Builtin.Equality public using (refl)
open import Data.List
open import Data.List.Membership.Propositional
import Data.List.Relation.Unary.Any as UAny
open UAny public using (here; there)
open import Function as Fun using (flip ; _∘_)

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
    id     : Map Dr Γ Γ
    weaken : Dr Γ A → Dr (B ∷ Γ) A

  infixl  10 _↑

  -- Lifts / extends a derivation map so a new topmost variable
  -- is mapped to a new topmost variable, and the rest is weakened.
  extend _↑ : Map Dr Γ Δ → Map Dr (A ∷ Γ) (A ∷ Δ)
  extend _ (here refl) = id (here refl)
  extend s (there i)   = weaken (s i)
  _↑ = extend

  wk : Map Dr Γ (A ∷ Γ)
  wk {Γ = _ ∷ _} = weaken ∘ id

record Subst (Dr : Deriv) : Set where
  field
    simple : Simple Dr
    app : Map Dr Γ Δ → Dr Γ A → Dr Δ A

  open Simple simple public

  _⊙_ : Map Dr Δ Κ → Map Dr Γ Δ → Map Dr Γ Κ
  Κ←Δ ⊙ Δ←Γ = app Κ←Δ ∘ Δ←Γ

record Embed (Dr₁ Dr₂ : Deriv) : Set where
  field
    simple : Simple Dr₁
    embed : Dr₁ Γ A → Dr₂ Γ A

  open Simple simple public

module VarSubst where
  subst : Subst _∋_
  subst = record
    { simple = record
      { id     = Fun.id
      ; weaken = there
      }
    ; app = λ f x → f x }

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
  simple = record { id    = var
                  ; weaken = rename VarSubst.wk
                  }

  idEmbed : Embed Tm Tm
  idEmbed = record { simple = simple
                   ; embed  = Fun.id
                   }

  subst : Map Tm Γ Δ → Tm Γ A → Tm Δ A
  subst = apply idEmbed

  tmSubst : Subst Tm
  tmSubst = record { simple = simple
                   ; app    = subst
                   }
