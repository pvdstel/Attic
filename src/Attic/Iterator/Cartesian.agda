module Attic.Iterator.Cartesian where

open import Attic.Iterator.Base using (Iterator; iterator; Step; Yield; Skip; Done)
open import Attic.Iterator.Bound using (bounded; _*_; _+_; _⊔_)

open import Data.Bool as Bool using (if_then_else_)
open import Data.Fin as Fin using (Fin; toℕ; fromℕ<)
open import Data.List as List using (List; _∷_; [])
open import Data.Maybe as Maybe using (Maybe; just; nothing)
open import Data.Nat as ℕ using (ℕ; _<?_; _≤?_; _>?_; _∸_)
open import Data.Product using (_×_; _,_)
open import Data.Vec as Vec using (Vec; _∷_; _∷ʳ_; []; allFin; foldr; lookup; sum)
open import Data.Vec.Relation.Unary.All as VecAll using (All; _∷_; []; map; reduce; zip)
open import Data.Vec.Properties using (lookup-allFin)
open import Function using (_$_; _∘_)
open import Level using (Level) renaming (suc to sucℓ)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; cong)
open import Relation.Nullary using (yes; no)

private
  variable
    ℓt ℓs ℓo : Level
    n : ℕ

  record IteratorSource (T : Set ℓt) : Set (ℓt Level.⊔ (sucℓ ℓs)) where
    constructor src
    field
      {S₀} : Set ℓs
      size : ℕ
      elements : Vec (Maybe T) size
      state : Maybe S₀
      next : S₀ → Step T {S₀}

  record CartesianState (n : ℕ) (Ts : Vec (Set ℓt) n) : Set (ℓt Level.⊔ (sucℓ ℓs)) where
    constructor cs
    field
      sources : All (λ i → IteratorSource {ℓs = ℓs} (lookup Ts i)) (allFin n)
      i : ℕ
      work : List (All (λ i → Fin (IteratorSource.size (VecAll.lookup i sources))) (allFin n))

  nextSource : {T : Set ℓt} → IteratorSource {ℓs = ℓs} T → IteratorSource T
  nextSource s@(src _ _ nothing _) = s
  nextSource s@(src size ts (just s0) next) with next s0
  ... | Done       = record s { state = nothing }
  ... | Skip  s1   = record s { size = (ℕ.suc size) ; elements = ts ∷ʳ nothing ; state = just s1 }
  ... | Yield s1 t = record s { size = (ℕ.suc size) ; elements = ts ∷ʳ just t  ; state = just s1 }

  generateWorkList : {n : ℕ} {Ts : Vec (Set ℓt) n} →
                     ℕ →
                     (sources : All (λ i → IteratorSource {ℓs = ℓs} (lookup Ts i)) (allFin n)) →
                     List (All (λ i → Fin (IteratorSource.size (VecAll.lookup i sources))) (allFin n))
  generateWorkList {n = n} sumTarget sources = generate' sumTarget srcIndices
    where
      srcIndices = allFin n

      optionalFin : ℕ → (size : ℕ) → List (Fin size)
      optionalFin _ ℕ.zero = []
      optionalFin m bound with m <? bound
      ... | yes m<n = fromℕ< m<n ∷ []
      ... | _       = []

      generate' : {m : ℕ} → ℕ → (inds : Vec (Fin n) m) → List (All (λ i → Fin (IteratorSource.size (VecAll.lookup i sources))) inds)
      generate' target [] = []
      generate' target (i ∷ []) = List.map (λ r → r ∷ []) lastResult
        where
          size = IteratorSource.size (VecAll.lookup i sources)
          lastResult = optionalFin target size
      generate' target (i ∷ ind') = concatenated
        where
          size = IteratorSource.size (VecAll.lookup i sources)
          candidates = List.allFin size
          usefulCandidates = List.takeWhile ((_≤? target) ∘ toℕ) candidates

          generateChildren : Fin size → _
          generateChildren c = List.map (λ d → c ∷ d) children
            where children = generate' (target ∸ (toℕ c)) ind'
          nestedLists = List.map generateChildren usefulCandidates
          concatenated = List.concat nestedLists

  lookupN : {n : ℕ} {Ts : Vec (Set ℓt) n} →
            (sources : All (λ i → IteratorSource {ℓs = ℓs} (lookup Ts i)) (allFin n)) →
            All (λ i → Fin (IteratorSource.size (VecAll.lookup i sources))) (allFin n) →
            All (λ i → Maybe (lookup Ts i)) (allFin n)
  lookupN {n = n} {Ts = Ts} sources indices = lookupN′ (allFin n)
    where
      lookupN′ : {m : ℕ} → (inds : Vec (Fin n) m) → All (λ i → Maybe (lookup Ts i)) inds
      lookupN′ [] = []
      lookupN′ (i ∷ inds) = eqT ∷ lookupN′ inds
        where
          eq-index  = cong (λ x → IteratorSource.size (VecAll.lookup x sources)) (lookup-allFin i)
          eq-lookup = cong (λ x → lookup Ts x) (lookup-allFin i)

          index = VecAll.lookup i indices
          elements = IteratorSource.elements $ VecAll.lookup i sources
          eqIndex = subst Fin eq-index index
          t = lookup elements eqIndex
          eqT = subst Maybe eq-lookup t

  AllMaybe→MaybeAll : {n : ℕ} (Ts : Vec (Set ℓt) n) →
                      All (λ i → Maybe (lookup Ts i)) (allFin n) →
                      Maybe (All (λ i → lookup Ts i) (allFin n))
  AllMaybe→MaybeAll {n = n} Ts mts = AllMaybe→MaybeAll′ (allFin n)
    where
      AllMaybe→MaybeAll′ : {m : ℕ} → (inds : Vec (Fin n) m) → Maybe (All (λ i → lookup Ts i) inds)
      AllMaybe→MaybeAll′ [] = just []
      AllMaybe→MaybeAll′ inds@(i ∷ inds′) = elem
        where
          eq-lookup = cong (λ x → lookup Ts x) (lookup-allFin i)
          mt = VecAll.lookup i mts
          eqMt = subst Maybe eq-lookup mt
          mts′ = AllMaybe→MaybeAll′ inds′
          elem : Maybe (All (λ i → lookup Ts i) inds)
          elem with eqMt | mts′
          ... | just t | just ts′ = just $ t ∷ ts′
          ... | _      | _        = nothing

cartesianₙ : {O : Set ℓo} {Ts : Vec (Set ℓt) n} →
             (All (λ i → lookup Ts i) (allFin n) → O) →
             All (λ i → Iterator {ℓs = ℓs} (lookup Ts i)) (allFin n) →
             Iterator O
cartesianₙ {n = n} {O = O} {Ts = Ts} fn iters = iterator bound s0 next
  where
    allBounds = reduce (Iterator.bound) iters
    boundMax = foldr _ _⊔_ (bounded 0) allBounds
    boundProduct = foldr _ _*_ (bounded 1) allBounds
    bound = boundProduct + (boundMax * (bounded n))

    S = CartesianState n Ts

    s0 : S
    s0 = record { sources = map (λ it → record { size = ℕ.zero
                                               ; elements = []
                                               ; state = just $ Iterator.state it
                                               ; next = Iterator.next it
                                               })
                                iters
                ; i = ℕ.zero
                ; work = []
                }

    next : S → Step O
    next (cs sources i []) = nextState
      where
        nextSources = map nextSource sources
        nextSizes = reduce IteratorSource.size nextSources
        sizeSum = sum nextSizes
        nextI = ℕ.suc i
        isDone = nextI >? sizeSum
        nextState : Step O
        nextState with isDone
        ... | yes _ = Done
        ... | no _  = Skip (record { sources = nextSources
                                    ; i = nextI
                                    ; work = generateWorkList {Ts = Ts} i nextSources
                                    })
    next s@(cs sources _ (w ∷ work')) = step
      where
        nextState = record s { work = work' }
        elements = lookupN {Ts = Ts} sources w
        values = AllMaybe→MaybeAll Ts elements
        step : Step O
        step with values
        ... | just vs = Yield nextState $ fn vs
        ... | nothing = Skip nextState

cartesianWith : {T₁ T₂ : Set ℓt} {O : Set ℓo} →
                (T₁ → T₂ → O) →
                Iterator {ℓs = ℓs} T₁ →
                Iterator {ℓs = ℓs} T₂ →
                Iterator O
cartesianWith {T₁ = T₁} {T₂ = T₂} {O = O} f i1 i2 =
  cartesianₙ
    {Ts = Ts}
    collect
    (i1 ∷ i2 ∷ [])
  where
    Ts = T₁ ∷ T₂ ∷ []
    collect : All (λ i → lookup Ts i) (allFin 2) → O
    collect (t1 ∷ t2 ∷ []) = f t1 t2

cartesian : {T₁ T₂ : Set ℓt} →
            Iterator {ℓs = ℓs} T₁ →
            Iterator {ℓs = ℓs} T₂ →
            Iterator (T₁ × T₂)
cartesian = cartesianWith _,_

cartesian₃With : {T₁ T₂ T₃ : Set ℓt} {O : Set ℓo} →
                 (T₁ → T₂ → T₃ → O) →
                 Iterator {ℓs = ℓs} T₁ →
                 Iterator {ℓs = ℓs} T₂ →
                 Iterator {ℓs = ℓs} T₃ →
                 Iterator O
cartesian₃With {T₁ = T₁} {T₂ = T₂} {T₃ = T₃} {O = O} f i1 i2 i3 =
  cartesianₙ
    {Ts = Ts}
    collect
    (i1 ∷ i2 ∷ i3 ∷ [])
  where
    Ts = T₁ ∷ T₂ ∷ T₃ ∷ []
    collect : All (λ i → lookup Ts i) (allFin 3) → O
    collect (t1 ∷ t2 ∷ t3 ∷ []) = f t1 t2 t3

cartesian₃ : {T₁ T₂ T₃ : Set ℓt} →
            Iterator {ℓs = ℓs} T₁ →
            Iterator {ℓs = ℓs} T₂ →
            Iterator {ℓs = ℓs} T₃ →
            Iterator (T₁ × T₂ × T₃)
cartesian₃ = cartesian₃With (λ t1 t2 t3 → t1 , t2 , t3)
