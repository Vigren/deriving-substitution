module Tools where

open import Agda.Builtin.String
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.Unit
open import Data.List
open import Data.Product using (_×_ ; _,_ ; proj₁ ; proj₂ ; map₁ ; map₂)
open import Function.Base
open import Function.Identity.Categorical using (applicative)
open import Reflection hiding (_≟_)
open import Reflection.DeBruijn
open import Reflection.Term
open import Reflection.Traversal

debug : List ErrorPart → TC ⊤
debug = debugPrint "tactic.substitution" 10

debugStr : String → TC ⊤
debugStr s = debug [ strErr s ]

typeErrorT : ∀ {a} {A : Set a} → Term → TC A
typeErrorT = typeError ∘ [_] ∘ termErr

typeErrorS : ∀ {a} {A : Set a} → String → TC A
typeErrorS s = typeError (strErr s ∷ [])

inContextTel : ∀ {a} {A : Set a} → Telescope → TC A → TC A
inContextTel tel = inContext (reverse (map proj₂ tel))

-- a₀, a₁, a₂  →  (2, a₀), (1, a₁), (0, a₂)
reverseCount : ∀ {a} {A : Set a} → List A → List (Nat × A)
reverseCount as = zip (downFrom $ length as) as

telView : Type → Telescope × Type
telView (pi a (abs x b)) = map₁ (_∷_ (x , a)) (telView b)
telView a                = [] , a

weakenPats : (by : Nat) → List (Arg Pattern) → List (Arg Pattern)
weakenPats = weakenFrom′ (traversePats applicative) 0

pattern var₀ x         = var x []
pattern var₁ x a       = var x (vArg a ∷ [])
pattern var₂ x a b     = var x (vArg a ∷ vArg b ∷ [])
pattern var₃ x a b c   = var x (vArg a ∷ vArg b ∷ vArg c ∷ [])
pattern var₄ x a b c d = var x (vArg a ∷ vArg b ∷ vArg c ∷ vArg d ∷ [])

pattern con₀ c         = con c []
pattern con₁ c x       = con c (vArg x ∷ [])
pattern con₂ c x y     = con c (vArg x ∷ vArg y ∷ [])
pattern con₃ c x y z   = con c (vArg x ∷ vArg y ∷ vArg z ∷ [])
pattern con₄ c x y z u = con c (vArg x ∷ vArg y ∷ vArg z ∷ vArg u ∷ [])

pattern def₀ f         = def f []
pattern def₁ f x       = def f (vArg x ∷ [])
pattern def₂ f x y     = def f (vArg x ∷ vArg y ∷ [])
pattern def₃ f x y z   = def f (vArg x ∷ vArg y ∷ vArg z ∷ [])
pattern def₄ f x y z u = def f (vArg x ∷ vArg y ∷ vArg z ∷ vArg u ∷ [])
