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

record EmbedCong (Dr Sup : Deriv) : Set₁ where
  field e : Embed Dr Sup
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

record EmbedId (Dr Sup : Deriv) : Set₁ where
  field e : Embed Dr Sup
  open Embed e public
  field weaken-id : weaken {Γ} {B} {A} ∘ id ≗ id ∘ there

  _≗ᴰ_ : (_ _ : Map Dr Γ Δ) → Set
  _≗ᴰ_ = Eq Dr
  _≗^_ : (_ _ : Map Sup Γ Δ) → Set
  _≗^_ = Eq Sup

  extId : extend {Γ} {Γ} id ≗ᴰ id {Γ = A ∷ Γ}
  extId (here refl) = refl
  extId (there i)   = weaken-id i


record TermSubstCong (Tm : Deriv) : Set₁ where
  field ts : TermSubst Tm
  open TermSubst ts
  ApplyCong : {Dr : Deriv} → (e : Embed Dr Tm) → Set
  ApplyCong {Dr} e = let open Embed e in
            ∀ {Γ Δ} {m₁ m₂ : Map Dr Γ Δ} → Eq Dr m₁ m₂
            → ∀ {A} → apply e m₁ {A} ≗ apply e m₂

  field applyCong : {Dr : Deriv} (ec : EmbedCong Dr Tm)
                  → ApplyCong (EmbedCong.e ec)
  field applyId : {Dr : Deriv} → (ei : EmbedId Dr Tm)
                → ApplyCong (EmbedId.e ei)
                → (e+id≡v : ∀ {Γ A}
                  → EmbedId.embed ei {Γ} {A} ∘ EmbedId.id ei ≡ var)
                → ∀ {Γ A} → apply (EmbedId.e ei) {Γ} {Γ} (EmbedId.id ei) {A}
                  ≗ Fun.id
  -- TODO: Can be weakened if just needed for Tm weaken-id
  field apply-var : ∀ {Dr} {e : Embed Dr Tm} {Γ Δ} {m : Map Dr Γ Δ} {A}
                  → apply e m ∘ var {Γ} {A} ≗ Embed.embed e ∘ m

  private
    _≗ⱽ_ : (_ _ : Map _∋_ Γ Δ) → Set
    _≗ⱽ_ = Eq _∋_
    _≗ᵀ_ : (_ _ : Map Tm Γ Δ) → Set
    _≗ᵀ_ = Eq Tm

  module Var where
    open VarSubst
    private variable m₁ m₂ : Map _∋_ Γ Δ

    e = record { simple = simple ; embed = var }
    ec : EmbedCong _∋_ Tm
    ec = record {e = e}

    renameCong : m₁ ≗ⱽ m₂ → ∀ {A} → rename m₁ {A} ≗ rename m₂
    renameCong = applyCong ec

    ei : EmbedId _∋_ Tm
    ei = record { e = e
                ; weaken-id = λ _ → refl
                }

    renameId : rename {Γ} {Γ} id {A} ≗ Fun.id
    renameId = applyId ei renameCong refl

  module Term where
    open Subst tmSubst
    private variable m₁ m₂ : Map Tm Γ Δ

    weaken-id : weaken {Γ} {A} {B} ∘ id ≗ id ∘ there
    weaken-id = apply-var

    e = record { simple = Subst.simple tmSubst
               ; embed = Fun.id
               }

    ec : EmbedCong Tm Tm
    ec = record { e = e }

    substCong : m₁ ≗ᵀ m₂ → ∀ {A} → subst m₁ {A} ≗ subst m₂
    substCong = applyCong ec

    ei : EmbedId Tm Tm
    ei = record { e = e
                ; weaken-id = weaken-id
                }

    substId : subst {Γ} {Γ} id {A} ≗ Fun.id
    substId = applyId ei substCong refl
