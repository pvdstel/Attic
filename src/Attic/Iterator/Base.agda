module Attic.Iterator.Base where

open import Attic.Iterator.Bound

open import Data.Bool using (Bool; true; false) public
open import Data.List using (List; [])
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (_×_; _,_; _,′_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit.Polymorphic using (⊤; tt)
open import Level using (Level; Lift; lift) renaming (suc to sucℓ; _⊔_ to _⊔ℓ_)

private
  variable
    ℓa ℓb ℓs ℓs₁ ℓs₂ : Level
    A : Set ℓa
    B : Set ℓb
    S : Set ℓs

data Step (A : Set ℓa) {S : Set ℓs} : Set (ℓa ⊔ℓ ℓs) where
  Done : Step A
  Skip : S → Step A
  Yield : S → A → Step A

record Iterator (A : Set ℓa) : Set (ℓa ⊔ℓ (sucℓ ℓs)) where
  constructor iterator
  field
    {S₀} : Set ℓs
    bound : Bound
    state : S₀
    next : S₀ → Step A {S₀}

-- An alternative definition of Iterator where the universe levels are forced
-- to be equal.
Iterator′ : Set ℓa → Set (sucℓ ℓa)
Iterator′ {ℓa} A = Iterator {ℓa} {ℓa} A

fromList : List A → Iterator A
fromList as0 = iterator (bounded (Data.List.length as0)) as0 next
  where
    next : List A → Step A
    next [] = Done
    next (a List.∷ as1) = Yield as1 a

-- An alternative to `fromList` where the state is always kept in level `zero`.
-- Performance is probably lower, but I have not measured that.
fromList′ : List A → Iterator {ℓs = Level.zero} A
fromList′ {A = A} as0 = iterator (bounded (Data.List.length as0)) zero next
  where
    index : (nextState : ℕ) → (index : ℕ) → List A → Step A {ℕ}
    index _ _ [] = Done
    index nextState zero (a List.∷ _) = Yield nextState a
    index nextState (suc n′) (_ List.∷ as) = index nextState n′ as

    next : ℕ → Step A
    next n = index (suc n) n as0

singleℓ : {ℓ : Level} → A → Iterator {ℓs = ℓ} A
singleℓ {A = A} {ℓ = ℓ} a = iterator (bounded 1) (just _) next
  where
    next : Maybe {ℓ} ⊤ → Step A
    next (just _) = Yield nothing a
    next nothing  = Done

single : A → Iterator A
single = singleℓ {ℓ = Level.zero}

emptyℓℓ : (ℓa ℓs : Level) → {A : Set ℓa} → Iterator {ℓa} {ℓs} A
emptyℓℓ _ _ = iterator (bounded 0) tt next
  where
    next : ⊤ → Step A
    next _ = Done

emptyℓ : (ℓ : Level) → {A : Set ℓ} → Iterator {ℓ} {ℓ} A
emptyℓ ℓ = emptyℓℓ ℓ ℓ

empty = emptyℓ Level.zero

infixr 5 _∷_
_∷_ : A → Iterator {_} {ℓs} A → Iterator A
_∷_ {A = A} a i₂ = iterator b s0 next
  where
    b = (bounded 1) + Iterator.bound i₂
    S₀ = A ⊎ (Iterator.S₀ i₂)
    s0 : S₀
    s0 = inj₁ a
    next′ = Iterator.next i₂

    next : S₀ → Step A
    next (inj₁ a′) = Yield (inj₂ (Iterator.state i₂)) a′
    next (inj₂ s1) with next′ s1
    ... | Done = Done
    ... | Skip s2 = Skip (inj₂ s2)
    ... | Yield s2 a′ = Yield (inj₂ s2) a′

infixr 5 _++_
_++_ : Iterator {_} {ℓs₁} A → Iterator {_} {ℓs₂} A → Iterator A
_++_ {A = A} i₁ i₂ = iterator b s0 next
  where
    b = Iterator.bound i₁ + Iterator.bound i₂
    S₀ = (Iterator.S₀ i₁) ⊎ (Iterator.S₀ i₂)
    s0 : S₀
    s0 = inj₁ (Iterator.state i₁)
    next₁ = Iterator.next i₁
    next₂ = Iterator.next i₂

    next : S₀ → Step A
    next (inj₁ s1₁) with next₁ s1₁
    ... | Done = next (inj₂ (Iterator.state i₂))
    ... | Skip s2₁ = Skip (inj₁ s2₁)
    ... | Yield s2₁ a₁ = Yield (inj₁ s2₁) a₁
    next (inj₂ s1₂) with next₂ s1₂
    ... | Done = Done
    ... | Skip s2₂ = Skip (inj₂ s2₂)
    ... | Yield s2₂ a₂ = Yield (inj₂ s2₂) a₂

fold : (A → B → B) → B → Iterator {_} {ℓs} A → ℕ → B
fold {A = A} {B = B} _⊕_ b (iterator {S} _ s0 next) n = collect n s0
  where
    collect : ℕ → S → B
    collect zero _ = b
    collect (suc n′) s1 with (next s1)
    ... | Done = b
    ... | Skip s2 = collect n′ s2
    ... | Yield s2 e = e ⊕ (collect n′ s2)

toList : Iterator {_} {ℓs} A → ℕ → (List A)
toList = fold List._∷_ []

filter : (A → Bool) → Iterator {_} {ℓs} A → Iterator A
filter {A = A} pred (iterator {S} b s0 next) = iterator b s0 next'
  where
    next' : S → Step A
    next' s1 with (next s1)
    ... | Done = Done
    ... | Skip s2 = Skip s2
    ... | Yield s2 a with (pred a)
    ...                 | true = Yield s2 a
    ...                 | false = Skip s2

map : (A → B) → Iterator {_} {ℓs₁} A → Iterator {ℓs = ℓs₁} B
map {A = A} {B = B} f (iterator {S} bound s0 next) = iterator bound s0 next′
  where
    next′ : S → Step B
    next′ s1 with (next s1)
    ... | Done = Done
    ... | Skip s2 = Skip s2
    ... | Yield s2 a = Yield s2 (f a)

map-syntax = map
syntax map-syntax (λ x → val) xs = for x of xs ∶ val

mapℓ : (ℓs₂ : Level) → (A → B) → Iterator {_} {ℓs₁} A → Iterator {_} {ℓs₁ ⊔ℓ ℓs₂} B
mapℓ {A = A} {B = B} ℓs₂ f (iterator {S} bound s0 next) = iterator bound (lift s0) next′
  where
    S₂ = Lift ℓs₂ S
    next′ : S₂ → Step B
    next′ (lift s1) with (next s1)
    ... | Done = Done
    ... | Skip s2 = Skip (lift s2)
    ... | Yield s2 a = Yield (lift s2) (f a)

take : (n : ℕ) → Iterator {_} {ℓs} A → Iterator A
take {A = A} n (iterator {S} b s0 next) = iterator (b ⊓ (bounded n)) (s0 ,′ n) next′
  where
    next′ : (S × ℕ) → Step A
    next′ (_ , zero) = Done
    next′ (s1 , (suc nn)) with (next s1)
    ... | Done = Done
    ... | Skip s2 = Skip (s2 ,′ nn)
    ... | Yield s2 a = Yield (s2 ,′ nn) a

first : Iterator {_} {ℓs} A → ℕ → (Maybe A)
first {A = A} (iterator {S} _ s0 next) n = collect n s0
  where
    collect : ℕ → S → Maybe A
    collect zero _ = nothing
    collect (suc n′) s1 with (next s1)
    ... | Done = nothing
    ... | Skip s2 = collect n′ s2
    ... | Yield _ a = just a

guard : Bool → Iterator ⊤
guard true  = single tt
guard false = empty

bound′ : ℕ → Iterator {_} {ℓs} A → ℕ
bound′ n (iterator  unbounded  _ _) = n
bound′ _ (iterator (bounded n) _ _) = n
