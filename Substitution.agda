module Substitution (Type : Set) where
open import Data.List
open import Data.List.Membership.Propositional
open import Data.List.Relation.Unary.Any using (here; there)
open import Function as Fun using (flip ; _∘_)
open import Relation.Binary.PropositionalEquality.Core using (refl)

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

record Embed (Dr₁ Dr₂ : Deriv) : Set where
  field
    simple : Simple Dr₁
    embed : Dr₁ Γ A → Dr₂ Γ A

  open Simple simple public

-- Composability of (not necessarily same-type) maps.
record Compose (Pos Pre : Deriv) {Res : Deriv} : Set where
  field
    app : Map Pos Γ Δ → ∀ {A} → Pre Γ A → Res Δ A

  infixl 9 _⊙_
  _⊙_ : Map Pos Δ Κ → Map Pre Γ Δ → Map Res Γ Κ
  Κ←Δ ⊙ Δ←Γ = app Κ←Δ ∘ Δ←Γ

varSimple = record { id     = Fun.id
                   ; weaken = there
                   }

record TermSubst (Tm : Deriv) : Set₁ where
  field
    var : Γ ∋ A → Tm Γ A
    apply : ∀ {Dr : Deriv} → Embed Dr Tm
          → ∀ {Γ Δ} → Map Dr Γ Δ
          → ∀ {A} → Tm Γ A
          → Tm Δ A

  varEmbed : Embed _∋_ Tm
  varEmbed = record { simple = varSimple
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

  preVarComp : ∀ {Dr} → Compose Dr _∋_
  preVarComp = record { app = Fun.id }

  preTmComp : ∀ {Dr} {e : Embed Dr Tm} → Compose Dr Tm
  preTmComp {e = e} = record { app = apply e }
