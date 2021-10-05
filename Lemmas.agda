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


module TermAuxiliaries (Tm : Deriv) where
  variable s₁ s₂ : Map Tm Γ Δ
  infix 4 _≗ᵀ_ _≗ˢ_
  _≗ˢ_ : (_ _ : Map Tm Γ Δ) → Set
  _≗ˢ_ = Eq Tm
  _≗ᵀ_ : (m₁ m₂ : ∀ {A} → Tm Γ A → Tm Δ A) → Set
  _≗ᵀ_ m₁ m₂ = ∀ {A} → m₁ {A} ≗ m₂ {A}

module DrAuxiliaries (Dr : Deriv) where
  variable d₁ d₂ : Map Dr Γ Δ
  infix 4 _≗ᴰ_
  _≗ᴰ_ : (_ _ : Map Dr Γ Δ) → Set
  _≗ᴰ_ = Eq Dr

-- A container of lemmas used by the applyCong function.
record CongAppArgs {Dr Tm : Deriv} (e : Embed Dr Tm) : Set₁ where
  open Embed e public
  open DrAuxiliaries Dr
  open TermAuxiliaries Tm

  extCong : d₁ ≗ᴰ d₂ → ∀ {P} → extend d₁ {P} ≗ᴰ extend d₂
  extCong m₁≗m₂ (here refl) = refl
  extCong m₁≗m₂ (there i)   = cong weaken (m₁≗m₂ i)

  extCongN : d₁ ≗ᴰ d₂ → ∀ {Pre} → extendN d₁ {Pre} ≗ᴰ extendN d₂ {Pre}
  extCongN m₁≗m₂ {Pre = []} = m₁≗m₂
  extCongN m₁≗m₂ {Pre = _ ∷ _} = extCong (extCongN m₁≗m₂)

record TermSubstCong {Tm : Deriv} (ts : TermSubst Tm) : Set₁ where
  open TermSubst ts
  open TermAuxiliaries Tm

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
  open DrAuxiliaries Dr
  open TermAuxiliaries Tm

  field tsc : TermSubstCong ts
  open TermSubstCong tsc using (applyCong)

  field weakenId : weaken {Γ} {A} {P} ∘ id ≡ id ∘ there
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
  open TermAuxiliaries Tm

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

record FuseAppArgs {DPos DPre DRes Tm} (ts : TermSubst Tm)
                   (ePos : Embed DPos Tm) (ePre : Embed DPre Tm) (eRes : Embed DRes Tm)
                   (c : Compose DPos DPre {DRes}) : Set₁ where
  open TermSubst ts
  open Embed ePos public using () renaming ( extendN to extendNPos
                                           ; extend to extendPos)
  open Embed ePre public using () renaming ( extendN to extendNPre
                                           ; extend to extendPre
                                           ; id to idPre
                                           ; weaken to weakenPre)
  open Embed eRes public using (embed) renaming ( extendN to extendNRes
                                                ; extend to extendRes
                                                ; weaken to weakenRes
                                                )
  open Compose c using (_⊙_) public
  open DrAuxiliaries DRes
  open TermAuxiliaries Tm

  field tsc : TermSubstCong ts
  open TermSubstCong tsc using (applyCong)

  field fuseApplyVar : ∀ {m₁ : Map DPre Γ Δ} {m₂ : Map DPos Δ Κ}
                    → apply ePos m₂ ∘ apply ePre m₁ ∘ var
                    -- ≗ˢ apply eRes (m₁ ⊙ m₂) ∘ var
                    ≗ˢ embed ∘ (m₂ ⊙ m₁)

  varCase : ∀ (m₁ : Map DPre Γ Δ) {m₂ : Map DPos Δ Κ}
            → apply ePos m₂ ∘ apply ePre m₁ ∘ var ≗ˢ embed ∘ (m₂ ⊙ m₁)
  varCase m₁ = fuseApplyVar {m₁ = m₁}

  field zeroExtend : ∀ {m₁ : Map DPre Γ Δ} {m₂ : Map DPos Δ Κ} {P}
                   → (extendPos m₂ {P} ⊙ extendPre m₁ {P}) (here refl)
                   ≡ extendRes (m₂ ⊙ m₁) (here refl)

  field sucExtend : ∀ {m₁ : Map DPre Γ Δ} {m₂ : Map DPos Δ Κ} {P}
                  → extendPos m₂ {P} ⊙ (weakenPre ∘ m₁)
                  ≗ᴰ weakenRes ∘ (m₂ ⊙ m₁)

  fuseExtN : ∀ {m₁ : Map DPre Γ Δ} {m₂ : Map DPos Δ Κ} (Pre)
           → extendNPos m₂ {Pre = Pre} ⊙ extendNPre m₁ {Pre = Pre}
           ≗ᴰ extendNRes (m₂ ⊙ m₁) {Pre = Pre}
  fuseExtN [] _                = refl
  fuseExtN (_ ∷ _) (here refl) = zeroExtend {m₁ = idPre}
  fuseExtN {m₁ = m₁} {m₂} (P ∷ Ps) (there i) = begin
      (extendNPos m₂ {P ∷ Ps} ⊙ extendNPre m₁ {P ∷ Ps}) (there i)
          ≡⟨ sucExtend {m₁ = extendNPre m₁ {Ps}} i ⟩
      weakenRes ((extendNPos m₂ ⊙ extendNPre m₁) i)
          ≡⟨ cong weakenRes (fuseExtN Ps i) ⟩
      weakenRes (extendNRes (m₂ ⊙ m₁) {Ps} i)
          ≡⟨⟩
      extendNRes (m₂ ⊙ m₁) {P ∷ Ps} (there i) ∎

  -- Scope inheriting case of fusion function
  applyFuseExtN : ∀ {Γ} {Δ} (Κ) {m₁ : Map DPre Γ Δ} {m₂ : Map DPos Δ Κ} {Pre}
                 → apply eRes (extendNPos m₂ ⊙ extendNPre m₁)
                 ≗ᵀ apply eRes (extendNRes (m₂ ⊙ m₁) {Pre})
  applyFuseExtN Κ t = applyCong _ (fuseExtN {Κ = Κ} _) t


record TermSubstFuse {Tm : Deriv} (ts : TermSubst Tm) : Set₁ where
  open TermSubst ts
  open TermAuxiliaries Tm
  open Embed varEmbed using () renaming (extend to varExtend)
  open Embed tmEmbed using () renaming (extend to tmExtend)
  field tsCong : TermSubstCong ts
  open TermSubstCong tsCong

  field fuse : ∀ {Pos Pre Res}
                 {ePos : Embed Pos Tm} {ePre : Embed Pre Tm} {eRes : Embed Res Tm}
                 {c : Compose Pos Pre}
                 (ca : FuseAppArgs ts ePos ePre eRes c) → let open Compose c in
               ∀ {Γ Δ Κ} {m₁ : Map Pre Γ Δ} {m₂ : Map Pos Δ Κ}
               → apply ePos m₂ ∘ apply ePre m₁ ≗ᵀ apply eRes (m₂ ⊙ m₁)

  field applyVar : ∀ {Dr : Deriv} {e : Embed Dr Tm} {Γ Δ} {m : Map Dr Γ Δ} {A}
                 → apply e m ∘ var ≡ Embed.embed e ∘ m {A}

  caVar : ∀ {Dr} {e : Embed Dr Tm} → FuseAppArgs ts e varEmbed e preVarComp
  caVar {e = e} = record
                  { tsc          = tsCong
                  ; fuseApplyVar = λ {_} {_} {_} {r} {m} i → begin
                                apply e m (rename r (var i))
                                      ≡⟨ cong (apply e m) (cong-app applyVar i) ⟩
                                apply e m (var (r i))
                                      ≡⟨ cong-app applyVar (r i) ⟩
                                Embed.embed e (m (r i)) ∎
                  ; zeroExtend = refl
                  ; sucExtend  = λ _ → refl
                  }

  ren-ren : rename r₂ ∘ rename r₁ ≗ᵀ rename (r₂ ∘ r₁)
  ren-ren = fuse caVar
  sub-ren : subst s₂ ∘ rename r₁ ≗ᵀ subst (s₂ ∘ r₁)
  sub-ren = fuse caVar

  renWeakenCom : rename (varExtend r₁ {P}) ∘ rename there
               ≗ᵀ rename there ∘ rename r₁
  renWeakenCom {r₁ = r₁} t = begin
    (rename (varExtend r₁) ∘ rename there) t ≡⟨ ren-ren t ⟩
    rename (varExtend r₁ ∘ there) t          ≡⟨⟩
    rename (there ∘ r₁) t                    ≡⟨ sym (ren-ren t) ⟩
    (rename there ∘ rename r₁) t             ∎

  caVarTm : FuseAppArgs ts varEmbed tmEmbed tmEmbed preTmComp
  caVarTm = record { tsc          = tsCong
                   ; fuseApplyVar = λ t → cong (rename _) (cong-app applyVar t)
                   ; zeroExtend   = cong-app applyVar (here refl)
                   ; sucExtend    = renWeakenCom ∘ _
                   }

  ren-sub : rename r₂ ∘ subst s₁ ≗ᵀ subst (rename r₂ ∘ s₁)
  ren-sub = fuse caVarTm

  subWeakenCom : subst (tmExtend s₁ {P}) ∘ rename there
               ≗ᵀ rename there ∘ subst s₁
  subWeakenCom {s₁ = s₁} t = begin
    (subst (tmExtend s₁) ∘ rename there) t ≡⟨ sub-ren t ⟩
    subst (tmExtend s₁ ∘ there) t          ≡⟨⟩
    subst (rename there ∘ s₁) t            ≡⟨ sym (ren-sub t) ⟩
    (rename there ∘ subst s₁) t            ∎

  caTmTm : FuseAppArgs ts tmEmbed tmEmbed tmEmbed preTmComp
  caTmTm = record { tsc          = tsCong
                  ; fuseApplyVar = λ t → cong (subst _) (cong-app applyVar t)
                  ; zeroExtend   = cong-app applyVar (here refl)
                  ; sucExtend    = subWeakenCom ∘ _
                  }

  sub-sub : subst s₂ ∘ subst s₁ ≗ᵀ subst (subst s₂ ∘ s₁)
  sub-sub = fuse caTmTm
