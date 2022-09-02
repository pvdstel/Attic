-- Test utilities.

module AtticTest.Util where

open import Data.Bool
open import Data.Nat
open import Relation.Binary.PropositionalEquality

isEven : ℕ → Bool
isEven zero = true
isEven (suc zero) = false
isEven (suc (suc n)) = isEven n

isOdd : ℕ → Bool
isOdd n = not (isEven n)

_ : isEven 0  ≡ true
_ = refl
_ : isEven 1  ≡ false
_ = refl
_ : isEven 12 ≡ true
_ = refl
_ : isEven 13 ≡ false
_ = refl

_ : isOdd 0  ≡ false
_ = refl
_ : isOdd 1  ≡ true
_ = refl
_ : isOdd 12 ≡ false
_ = refl
_ : isOdd 13 ≡ true
_ = refl
