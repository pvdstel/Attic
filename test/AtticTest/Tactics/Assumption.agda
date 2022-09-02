module AtticTest.Tactics.Assumption where

open import Attic.GlobalImports
open import Attic.Macro
open import Attic.Monad
open import Attic.Tactics.Assumption
open import Attic.Tactics.Intro

open import Data.Bool using (Bool)
open import Data.Nat using (ℕ)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

macro
  assumption′ = asMacro assumption
  introAssumption = asMacro $ intro >> assumption

test1 : ℕ → ℕ
test1 n = assumption′

test1Expected : ℕ → ℕ
test1Expected n = n

_ : test1 ≡ test1Expected
_ = refl

test2 : ℕ → ℕ → ℕ
test2 n m = assumption′

test2Expected : ℕ → ℕ → ℕ
test2Expected n m = m -- `m` because it's the closest, in terms of De Bruijn indices

_ : test2 ≡ test2Expected
_ = refl

test3 : ℕ → Bool → ℕ
test3 n b = assumption′

test3Expected : ℕ → Bool → ℕ
test3Expected n b = n

_ : test3 ≡ test3Expected
_ = refl

test4 : Bool → ℕ → ℕ
test4 b n = assumption′

test4Expected : Bool → ℕ → ℕ
test4Expected b n = n

_ : test4 ≡ test4Expected
_ = refl

test5 : ∀ {a} {A : Set a} → A → ℕ → A
test5 a n = assumption′

test5Expected : ∀ {a} {A : Set a} → A → ℕ → A
test5Expected a n = a

_ : ∀ {a} {A : Set a} → test5 {A = A} ≡ test5Expected
_ = refl
