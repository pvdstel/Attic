module AtticTest.Tactics.Intro where

open import Attic.BasicTactics
open import Attic.GlobalImports
open import Attic.Macro
open import Attic.Monad
open import Attic.Tactics.Intro

open import AtticTest.Tactics.SimpleTestTactics

open import Data.Nat using (ℕ)
open import Relation.Binary.PropositionalEquality using (refl; _≡_)

macro
  introAdmit = asMacro $ intro >> admitAll
  introFill = asMacro $ intro >> (fillNat 5)
  intro⟫FillVar0 = asMacro $ intro >> fillVar0
  introDbg = asMacro $ intro >> debugLogGoalContext
  repeatedIntro = asMacro $ repeatTry 10 intro >> (fillNat 5)

-- Basic tests

testNat : ℕ → ℕ
testNat = introFill
_ : testNat ≡ (λ _ → 5)
_ = refl

testVar : ℕ → ℕ
testVar = intro⟫FillVar0
_ : testVar ≡ λ n → n
_ = refl

-- Repeated tests

repeated0Test : ℕ
repeated0Test = repeatedIntro
_ : repeated0Test ≡ 5
_ = refl

repeated1Test : ℕ → ℕ
repeated1Test = repeatedIntro
_ : repeated1Test ≡ (λ n → 5)
_ = refl

repeated5Test : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ
repeated5Test = repeatedIntro
_ : repeated5Test ≡ (λ n1 n2 n3 n4 n5 → 5)
_ = refl
