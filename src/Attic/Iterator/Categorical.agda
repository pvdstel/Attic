module Attic.Iterator.Categorical where

open import Attic.Iterator.Base
open import Attic.Iterator.Bound using (Bound)
open import Attic.Iterator.Concat

open import Category.Functor using (RawFunctor)
open import Level using (Level; _⊔_) renaming (suc to sucℓ)

private
  variable
    ℓa ℓb ℓs ℓs₁ ℓs₂ : Level

bind : {A : Set ℓa} {B : Set ℓb} →
       Iterator {ℓs = ℓs₁} A →
       (A → Iterator {ℓs = ℓs₂} B) →
       Iterator B
bind as g = concat (map g as)

then : {A : Set ℓa} {B : Set ℓb} →
       Iterator {ℓs = ℓs₁} A →
       Iterator {ℓs = ℓs₂} B →
       Iterator B
then as bs = bind as (λ _ → bs)

infixl 1 _>>=_ _>>_
_>>=_ = bind
_>>_  = then
return = single

instance
  functorAttic : RawFunctor (Iterator {ℓa = ℓa} {ℓs = ℓs})
  functorAttic = record { _<$>_ = map }
