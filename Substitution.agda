module Substitution (Type : Set) where
open import Agda.Builtin.Equality using (refl)
open import Data.List
open import Data.List.Membership.Propositional
open import Data.List.Relation.Unary.Any using (here; there)
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
    A B C P : Type
    Γ Δ Κ Pre : Context
open Variables

record Simple (Dr : Deriv) : Set where
  field
    id     : Map Dr Γ Γ
    weaken : Dr Γ A → Dr (P ∷ Γ) A

  infixl  10 _↑

  -- Lifts / extends a derivation map so a new topmost variable
  -- is mapped to a new topmost variable, and the rest is weakened.
  extend _↑ : Map Dr Γ Δ → ∀ {P} → Map Dr (P ∷ Γ) (P ∷ Δ)
  extend _ (here refl) = id (here refl)
  extend s (there i)   = weaken (s i)
  _↑ = extend

  extendN : Map Dr Γ Δ → ∀ {Pre} → Map Dr (Pre ++ Γ) (Pre ++ Δ)
  extendN m {Pre = []}    = m
  extendN m {Pre = _ ∷ _} = extend (extendN m)

  wk : Map Dr Γ (P ∷ Γ)
  wk {Γ = _ ∷ _} = weaken ∘ id

record Subst (Dr : Deriv) : Set where
  field
    simple : Simple Dr
    app : Map Dr Γ Δ → ∀ {A} → Dr Γ A → Dr Δ A

  open Simple simple public

  _⊙_ : Map Dr Δ Κ → Map Dr Γ Δ → Map Dr Γ Κ
  Κ←Δ ⊙ Δ←Γ = app Κ←Δ ∘ Δ←Γ

record Embed (Dr₁ Dr₂ : Deriv) : Set where
  field
    simple : Simple Dr₁
    embed : Dr₁ Γ A → Dr₂ Γ A

  open Simple simple public

varSubst : Subst _∋_
varSubst = record { simple = record
                    { id     = Fun.id
                    ; weaken = there
                    }
                  ; app = Fun.id
                  }

record TermSubst (Tm : Deriv) : Set₁ where
  field
    var : Γ ∋ A → Tm Γ A
    apply : ∀ {Dr : Deriv} → Embed Dr Tm
          → ∀ {Γ Δ} → Map Dr Γ Δ
          → ∀ {A} → Tm Γ A
          → Tm Δ A

  varEmbed : Embed _∋_ Tm
  varEmbed = record { simple = Subst.simple varSubst
                    ; embed  = var
                    }

  rename : Map _∋_ Γ Δ → ∀ {A} → Tm Γ A → Tm Δ A
  rename = apply varEmbed

  tmEmbed : Embed Tm Tm
  tmEmbed = record { simple = record { id     = var
                                     ; weaken = rename there
                                     }
                   ; embed  = Fun.id
                   }

  subst : Map Tm Γ Δ → ∀ {A} → Tm Γ A → Tm Δ A
  subst = apply tmEmbed

  tmSubst : Subst Tm
  tmSubst = record { simple = Embed.simple tmEmbed
                   ; app    = subst
                   }
