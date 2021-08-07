module Lemmas (Type : Set) where

open import Substitution (Type)
open Variables
import Function as Fun
open Fun using (_$_ ; _∘_)
open import Data.List
open import Data.List.Membership.Propositional
open import Data.List.Membership.Setoid using (_∈_)
open import Data.List.Relation.Unary.Any
  using (here ; there ; Any)
open import Relation.Binary.PropositionalEquality
            hiding (subst)

open ≡-Reasoning

-- Pointwise equality on maps.
Eq : (Dr : Deriv) → (m₁ m₂ : Map Dr Γ Δ) → Set
Eq _ m₁ m₂ = ∀ {A} → m₁ {A} ≗ m₂ {A}

variable r₁ r₂ : Map _∋_ Γ Δ
infix 4 _≗ᴿ_
_≗ᴿ_ : (_ _ : Map _∋_ Γ Δ) → Set
_≗ᴿ_ = Eq _∋_


module TermAuxilliaries (Tm : Deriv) where
  variable s₁ s₂ : Map Tm Γ Δ
  infix 4 _≗ᵀ_ _≗ˢ_
  _≗ˢ_ : (_ _ : Map Tm Γ Δ) → Set
  _≗ˢ_ = Eq Tm
  _≗ᵀ_ : (m₁ m₂ : ∀ {A} → Tm Γ A → Tm Δ A) → Set
  _≗ᵀ_ m₁ m₂ = ∀ {A} → m₁ {A} ≗ m₂ {A}

module DrAuxilliaries (Dr : Deriv) where
  variable d₁ d₂ : Map Dr Γ Δ
  infix 4 _≗ᴰ_
  _≗ᴰ_ : (_ _ : Map Dr Γ Δ) → Set
  _≗ᴰ_ = Eq Dr

-- A container of lemmas used by the applyCong function.
record CongAppArgs {Dr Tm : Deriv} (e : Embed Dr Tm) : Set₁ where
  open Embed e public
  open DrAuxilliaries Dr
  open TermAuxilliaries Tm

  extCong : d₁ ≗ᴰ d₂ → ∀ {P} → extend d₁ {P} ≗ᴰ extend d₂
  extCong m₁≗m₂ (here refl) = refl
  extCong m₁≗m₂ (there i)   = cong weaken (m₁≗m₂ i)

  extCongN : d₁ ≗ᴰ d₂ → ∀ {Pre} → extendN d₁ {Pre} ≗ᴰ extendN d₂ {Pre}
  extCongN m₁≗m₂ {Pre = []} = m₁≗m₂
  extCongN m₁≗m₂ {Pre = _ ∷ _} = extCong (extCongN m₁≗m₂)

record TermSubstCong {Tm : Deriv} (ts : TermSubst Tm) : Set₁ where
  open TermSubst ts
  open TermAuxilliaries Tm

  field applyCong : ∀ {Dr : Deriv} {e : Embed Dr Tm} (ec : CongAppArgs e)
                  → ∀ {Γ Δ} {m₁ m₂ : Map Dr Γ Δ} → Eq Dr m₁ m₂
                  → apply e m₁ ≗ᵀ apply e m₂

  renameCong : r₁ ≗ᴿ r₂ → rename r₁ ≗ᵀ rename r₂
  renameCong = applyCong _

  substCong : s₁ ≗ˢ s₂ → subst s₁ ≗ᵀ subst s₂
  substCong = applyCong _

-- A container of lemmas used by the applyId function.
record IdAppArgs {Dr Tm : Deriv} (ts : TermSubst Tm) (e : Embed Dr Tm) : Set₁ where
  open TermSubst ts
  open Embed e public
  open DrAuxilliaries Dr
  open TermAuxilliaries Tm

  field tsc : TermSubstCong ts
  open TermSubstCong tsc using (applyCong)

  field weakenId : weaken {Γ} {B} {A} ∘ id ≡ id ∘ there
  field e+id=var : embed {Γ} ∘ id ≗ˢ var

  extId : ∀ {P} → extend {Γ} {Γ} id ≗ᴰ id {Γ = P ∷ Γ}
  extId (here refl) = refl
  extId (there i)   = cong-app weakenId i

  extIdN : ∀ Pre → extendN {Γ} {Γ} id ≗ᴰ id {Γ = Pre ++ Γ}
  extIdN [] _                 = refl
  extIdN (_ ∷ _)  (here refl) = refl
  extIdN (_ ∷ Ps) (there t)   = trans (cong weaken (extIdN Ps t))
                                      (cong-app weakenId t)

  appExtCong : ∀ Γ → apply e (extendN {Γ} id {Pre}) ≗ᵀ apply e id
  appExtCong {Pre = Pre} _ = applyCong _ (extIdN Pre)

record TermSubstId {Tm : Deriv} (ts : TermSubst Tm) : Set₁ where
  field tsCong : TermSubstCong ts
  open TermSubst ts
  open TermAuxilliaries Tm

  field applyId : ∀ {Dr} {e : Embed Dr Tm} (ia : IdAppArgs ts e) {Γ}
                → apply e {Γ} {Γ} (Embed.id e) ≗ᵀ Fun.id
  field applyVar : ∀ {Dr} {e : Embed Dr Tm} {Γ Δ} {m : Map Dr Γ Δ} {A}
                 → apply e m ∘ var ≡ Embed.embed e ∘ m {A}

  renameId : rename {Γ} {Γ} Fun.id ≗ᵀ Fun.id
  renameId = applyId record { tsc        = tsCong
                            ; weakenId   = refl
                            ; e+id=var   = λ _ → refl
                            }

  substId : subst {Γ} {Γ} var ≗ᵀ Fun.id
  substId = applyId record { tsc        = tsCong
                           ; weakenId   = applyVar
                           ; e+id=var   = λ _ → refl
                           }
