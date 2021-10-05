module Tests where
open import Data.List.Base
open import Data.Nat using (ℕ)

infixr 6 _⇒_
infixl 7 _+_

data Type : Set where
  _⇒_ : Type → Type → Type
  _+_ : Type → Type → Type

open import Tactic
open import Substitution (Type)
open import Lemmas (Type)
open Variables

module Double where
  data Tm (Γ : Context) : Type → Set where
    var : Γ ∋ A → Tm Γ A
    app : Tm Γ (A ⇒ B) → Tm Γ A → Tm Γ B
    abs : Tm (A ∷ A ∷ Γ) B → Tm Γ (A ⇒ B)

  ts : TermSubst Tm
  ts = deriveSubst

  tsi : TermSubstId ts
  tsi = deriveTSId

  tsf : TermSubstFuse ts
  tsf = deriveTSFuse

module NoParam where
  data Tm : Context → Type → Set where
    var : Γ ∋ A → Tm Γ A
    app : Tm Γ (B ⇒ A) → Tm Γ B → Tm Γ A

  ts : TermSubst Tm
  ts = deriveSubst

  tsi : TermSubstId ts
  tsi = deriveTSId

  tsf : TermSubstFuse ts
  tsf = deriveTSFuse

module TwoParam where
  data Tm (Γ : Context) (A : Type) : Set where
    var : Γ ∋ A → Tm Γ A
    app : Tm Γ (B ⇒ A) → Tm Γ B → Tm Γ A

  ts : TermSubst Tm
  ts = deriveSubst

  tsi : TermSubstId ts
  tsi = deriveTSId

  tsf : TermSubstFuse ts
  tsf = deriveTSFuse

-- For whole lists that normalizes to conses
module ContextConcatenation where
  data Tm (Γ : Context) (A : Type) : Set where
    var : Γ ∋ A → Tm Γ A
    c : Tm ( A ∷ [ A ] ++ Γ) A → Tm Γ A

  ts : TermSubst Tm
  ts = deriveSubst

  tsi : TermSubstId ts
  tsi = deriveTSId

  tsf : TermSubstFuse ts
  tsf = deriveTSFuse

module Constant where
  data Tm (Γ : Context) : Type → Set where
    var : Γ ∋ A → Tm Γ A
    con : ℕ → Tm Γ A → Tm Γ A

  ts : TermSubst Tm
  ts = deriveSubst

  tsi : TermSubstId ts
  tsi = deriveTSId

  tsf : TermSubstFuse ts
  tsf = deriveTSFuse

-- A subterm that does not inherit parent scope
module FreshScope where
  data Tm (Γ : Context) : Type → Set where
    var : Γ ∋ A → Tm Γ A
    st : Tm (A ∷ []) A → Tm Γ A

  ts : TermSubst Tm
  ts = deriveSubst

  tsi : TermSubstId ts
  tsi = deriveTSId

  tsf : TermSubstFuse ts
  tsf = deriveTSFuse

module LetLetRec where
  data Tm (Γ : Context) : Type → Set where
    var : Γ ∋ A → Tm Γ A
    reclet : Tm (A ∷ Γ) A → Tm Γ A
    Let_In_ : Tm Γ A → Tm (A ∷ Γ) B → Tm Γ B

  ts : TermSubst Tm
  ts = deriveSubst

  tsi : TermSubstId ts
  tsi = deriveTSId

  tsf : TermSubstFuse ts
  tsf = deriveTSFuse
