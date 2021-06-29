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


-- A container of lemmas used by the applyCong function.
record CongAppArgs {Dr Sup : Deriv} (e : Embed Dr Sup) : Set₁ where
  open Embed e public

  _≗ᴰ_ : (_ _ : Map Dr Γ Δ) → Set
  _≗ᴰ_ = Eq Dr
  _≗^_ : (_ _ : Map Sup Γ Δ) → Set
  _≗^_ = Eq Sup

  extCong : ∀ {m₁ m₂ : Map Dr Γ Δ} → m₁ ≗ᴰ m₂
          → ∀ {A} → extend m₁ {A} ≗ᴰ extend m₂
  extCong m₁≗m₂ (here refl) = refl
  extCong m₁≗m₂ (there i)   = cong weaken (m₁≗m₂ i)

  extCongN : {m₁ m₂ : Map Dr Γ Δ} → m₁ ≗ᴰ m₂
           → ∀ {Κ} → extendN m₁ {Κ} ≗ᴰ extendN m₂
  extCongN m₁≗m₂ {Κ = []} = m₁≗m₂
  extCongN m₁≗m₂ {Κ = _ ∷ _} = extCong (extCongN m₁≗m₂)

  embedCong : {m₁ m₂ : Map Dr Γ Δ} → m₁ ≗ᴰ m₂
            → (embed ∘ m₁) ≗^ (embed ∘ m₂)
  embedCong m₁≗m₂ i = cong embed (m₁≗m₂ i)


record TermSubstCong {Tm : Deriv} (ts : TermSubst Tm) : Set₁ where
  open TermSubst ts

  field applyCong : ∀ {Dr : Deriv} {e : Embed Dr Tm} (ec : CongAppArgs e)
                  → ∀ {Γ Δ} {m₁ m₂ : Map Dr Γ Δ} → Eq Dr m₁ m₂
                  → ∀ {A} → apply e m₁ {A} ≗ apply e m₂

  renameCong : ∀ {m₁ m₂ : Map _∋_ Γ Δ} → Eq _∋_ m₁ m₂ → ∀ {A} → rename m₁ {A} ≗ rename m₂
  renameCong = applyCong _

  substCong : ∀ {m₁ m₂ : Map Tm Γ Δ} → Eq Tm m₁ m₂ → ∀ {A} → subst m₁ {A} ≗ subst m₂
  substCong = applyCong _

-- A container of lemmas used by the applyId function.
record IdAppArgs {Dr Tm : Deriv} (ts : TermSubst Tm) (e : Embed Dr Tm) : Set₁ where
  open TermSubst ts
  open Embed e public
  field tsc : TermSubstCong ts
  open TermSubstCong tsc using (applyCong)

  _≗ᴰ_ : (_ _ : Map Dr Γ Δ) → Set
  _≗ᴰ_ = Eq Dr

  field weakenId : weaken {Γ} {B} {A} ∘ id ≡ id ∘ there
  field e+id=var : ∀ {Γ A} → embed {Γ} {A} ∘ id ≗ var

  extId : extend {Γ} {Γ} id ≗ᴰ id {Γ = A ∷ Γ}
  extId (here refl) = refl
  extId (there i)   = cong-app weakenId i

  extIdN : extendN {Γ} {Γ} id ≗ᴰ id {Γ = Κ ++ Γ}
  extIdN {_} {[]} _              = refl
  extIdN {_} {_ ∷ _} (here refl) = refl
  extIdN {Γ} {_ ∷ _} (there t)   = trans (cong weaken (extIdN {Γ} t))
                                         (cong-app weakenId t)

  appExtCong : ∀ {Κ} → apply e (extendN {Γ} id {Κ}) {A} ≗ apply e id
  appExtCong {Γ} = applyCong _ (extIdN {Γ})

record TermSubstId {Tm : Deriv} (ts : TermSubst Tm) : Set₁ where
  field tsCong : TermSubstCong ts
  open TermSubst ts

  field applyId : ∀ {Dr} {e : Embed Dr Tm} (ia : IdAppArgs ts e) {Γ A}
                → apply e {Γ} {Γ} (Embed.id e) {A} ≗ Fun.id
  field applyVar : ∀ {Dr : Deriv} {e : Embed Dr Tm} {Γ Δ} {m : Map Dr Γ Δ} {A}
                 → apply e m ∘ var {Γ} {A} ≡ Embed.embed e ∘ m

  module _ where
    open VarSubst using (id)
    renameId : rename {Γ} {Γ} id {A} ≗ Fun.id
    renameId = applyId record { tsc        = tsCong
                              ; weakenId   = refl
                              ; e+id=var   = λ _ → refl
                              }

  module _ where
    open Subst tmSubst using (id)
    substId : subst {Γ} {Γ} id {A} ≗ Fun.id
    substId = applyId record { tsc        = tsCong
                             ; weakenId   = applyVar
                             ; e+id=var   = λ _ → refl
                             }
