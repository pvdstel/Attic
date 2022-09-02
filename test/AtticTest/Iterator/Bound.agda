module AtticTest.Iterator.Bound where

open import Attic.Iterator.Bound

open import Relation.Binary.PropositionalEquality

-- _+_

_ : bounded 10 + bounded 4 ≡ bounded 14
_ = refl

_ : bounded 10 + unbounded ≡ unbounded
_ = refl

_ : unbounded + bounded 4 ≡ unbounded
_ = refl

-- _*_

_ : bounded 10 * bounded 4 ≡ bounded 40
_ = refl

_ : bounded 10 * unbounded ≡ unbounded
_ = refl

_ : unbounded * bounded 4 ≡ unbounded
_ = refl

-- _∸_

_ : bounded 10 ∸ bounded 4 ≡ bounded 6
_ = refl

_ : bounded 4 ∸ bounded 10 ≡ bounded 0
_ = refl

_ : bounded 10 ∸ unbounded ≡ unbounded
_ = refl

_ : unbounded ∸ bounded 4 ≡ unbounded
_ = refl

-- _⊔_ (max)

_ : bounded 10 ⊔ bounded 4 ≡ bounded 10
_ = refl

_ : bounded 10 ⊔ unbounded ≡ unbounded
_ = refl

_ : unbounded ⊔ bounded 4 ≡ unbounded
_ = refl

-- _⊓_ (min)

_ : bounded 10 ⊓ bounded 4 ≡ bounded 4
_ = refl

_ : bounded 10 ⊓ unbounded ≡ bounded 10
_ = refl

_ : unbounded ⊓ bounded 4 ≡ bounded 4
_ = refl
