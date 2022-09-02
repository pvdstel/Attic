module AtticTest.Tactics.Destruct where

open import Attic.BasicTactics
open import Attic.GlobalImports
open import Attic.Macro
open import Attic.Monad
open import Attic.Tactics.Destruct

open import AtticTest.Tactics.SimpleTestTactics

open import Data.Bool using (Bool; true; false)
open import Data.List using (List; []; _∷_)
open import Data.Nat using (ℕ; zero; suc)
open import Data.String using (String)
open import Function using (case_of_)
open import Reflection using (Term)
open import Relation.Binary.PropositionalEquality using (refl; _≡_)

private
  DiscriminatingType : ℕ → Set
  DiscriminatingType zero = List ℕ
  DiscriminatingType (suc b) = Bool

macro
  testDestruct = asMacro $ (destructIndex 0) ∶▷⁺· (fillNat 123)

testDestruct∶▷⁺· : ℕ → ℕ
testDestruct∶▷⁺· blurp = testDestruct

expectedDestruct∶▷⁺· : ℕ → ℕ
expectedDestruct∶▷⁺· blurp = case blurp of λ
  { ℕ.zero    → 123
  ; (ℕ.suc n) → 123
  }

extensionalityDestruct∶▷⁺· : ∀ (n) → testDestruct∶▷⁺· n ≡ expectedDestruct∶▷⁺· n
extensionalityDestruct∶▷⁺·  ℕ.zero   = refl
extensionalityDestruct∶▷⁺· (ℕ.suc n) = refl
