module Attic.Iterator.Bound where

import Data.Nat as ℕ

data Bound : Set where
  unbounded : Bound
  bounded : ℕ.ℕ → Bound

private
  Op₂ = Bound → Bound → Bound

-- Addition.
_+_ : Op₂
_+_ unbounded _ = unbounded
_+_ _ unbounded = unbounded
_+_ (bounded n) (bounded m) = bounded (n ℕ.+ m)

-- Multiplication.
_*_ : Op₂
_*_ unbounded _ = unbounded
_*_ _ unbounded = unbounded
_*_ (bounded n) (bounded m) = bounded (n ℕ.* m)

-- Subtraction
_∸_ : Op₂
_∸_ unbounded _ = unbounded
_∸_ _ unbounded = unbounded
_∸_ (bounded n) (bounded m) = bounded (n ℕ.∸ m)

-- Maximum.
_⊔_ : Op₂
_⊔_ unbounded _ = unbounded
_⊔_ _ unbounded = unbounded
_⊔_ (bounded n) (bounded m) = bounded (n ℕ.⊔ m)

-- Minimum.
_⊓_ : Op₂
_⊓_ unbounded x = x
_⊓_ x unbounded = x
_⊓_ (bounded n) (bounded m) = bounded (n ℕ.⊓ m)
