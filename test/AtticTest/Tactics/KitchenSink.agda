-- Combine many different tests: a kitchen sink

module AtticTest.Tactics.KitchenSink where

open import Attic.BasicTactics
open import Attic.Development
open import Attic.GlobalImports
open import Attic.Macro
open import Attic.Monad
open import Attic.Tactics.Assumption
open import Attic.Tactics.Destruct
open import Attic.Tactics.Intro

open import AtticTest.Tactics.SimpleTestTactics

open import Data.Bool using (if_then_else_)
open import Data.List using (length)
open import Data.Nat using (ℕ; _≥?_)
open import Data.String using (String)
open import Function using (case_of_)
open import Reflection using (Term)
open import Relation.Binary.PropositionalEquality using (refl; _≡_)
open import Relation.Nullary.Decidable using (isYes)

-- Only uses assumption if the context is large enough
failableAssumption : ℕ → Attic ⊤
failableAssumption n = do
  context ← getContext
  if isYes ((length context) ≥? n)
       then assumption
       else (failure $ errStr "Sadly not large enough.")

macro
  introDestructAssume = asMacro $ intro >> destructIndex 0 ∶▷⁺· assumption
  introDestructAssume′ = asMacro $ intro >> destructIndex 0 ∶▷⁺· admitAll
  introDestructFailable = asMacro $ intro >> destructIndex 0 ∶▷⁺· (tryCatch (failableAssumption 2) (fillNat 23))

testDestructAssume : ℕ → ℕ
testDestructAssume = introDestructAssume

expectedDestructAssume : ℕ → ℕ
expectedDestructAssume = λ z →
  Attic.Tactics.Destruct.case─match z of
    (λ {  ℕ.zero   → z
       ; (ℕ.suc n) → n
       })

extensionalityDestructAssume : ∀ (n) → testDestructAssume n ≡ expectedDestructAssume n
extensionalityDestructAssume ℕ.zero = refl
extensionalityDestructAssume (ℕ.suc c) = refl

testDestructFailable : ℕ → ℕ
testDestructFailable = introDestructFailable

expectedDestructFailable : ℕ → ℕ
expectedDestructFailable = λ z →
  Attic.Tactics.Destruct.case─match z of
    (λ {  ℕ.zero   → 23
       ; (ℕ.suc n) → n
       })

extensionalityDestructFailable : ∀ (n) → testDestructFailable n ≡ expectedDestructFailable n
extensionalityDestructFailable ℕ.zero = refl
extensionalityDestructFailable (ℕ.suc c) = refl
