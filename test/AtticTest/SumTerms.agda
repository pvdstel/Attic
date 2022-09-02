-- A test tool, helped for developing the restricted integer compositions.

{-# OPTIONS --guardedness --rewriting #-}

module AtticTest.SumTerms where

open import Data.Bool using (true)
open import Data.Fin as Fin using (Fin; toℕ; fromℕ; fromℕ<)
open import Data.List as List using (List; _∷_; [])
open import Data.Nat as ℕ using (ℕ; _≡ᵇ_; _<?_; _≤?_; _>?_; _∸_)
open import Data.Product using (_,_)
open import Data.Vec as Vec using (Vec; _∷_; []; allFin; foldr; lookup; sum; toList)
open import Data.Vec.Relation.Unary.All as VecAll using (All; _∷_; []; reduce; zip)
open import Function using (_$_; _∘_)
open import Relation.Nullary using (yes)

open import Data.Nat.Show as ℕ using (show)
open import Data.Fin.Show as Fin using (show)
open import Data.String using (String; intersperse) renaming (_++_ to _str+_)
import Debug.Trace
open import IO

trace : ∀ {a} {A : Set a} → String → A → A
trace str a = a
-- trace str a = Debug.Trace.trace str a

record SizedThing : Set where
  constructor st
  field
    size : ℕ

sumTerms : {n : ℕ} →
           ℕ →
           (things : All (λ _ → SizedThing) (allFin n)) →
           List (All (λ i → Fin (SizedThing.size (VecAll.lookup i things))) (allFin n))
sumTerms _ [] = []
sumTerms {n = n} sumTarget bounds@(_ ∷ _) = generate' sumTarget srcIndices
  where
    srcIndices = allFin n

    optionalFin : ℕ → (size : ℕ) → List (Fin size)
    optionalFin _ ℕ.zero = []
    optionalFin m bound with m <? bound
    ... | yes m<n = trace "opt yea" $ fromℕ< m<n ∷ []
    ... | _       = trace "opt nay" $ []

    generate' : {m : ℕ} → ℕ → (inds : Vec (Fin n) m) → List (All (λ i → Fin (SizedThing.size (VecAll.lookup i bounds))) inds)
    generate' target [] = trace "end" []
    generate' target (i ∷ []) = List.map (λ r → r ∷ []) lastResult
      where
        size = trace ("[index " str+ (Fin.show i) str+ "]") SizedThing.size $ VecAll.lookup i bounds
        lastResult = trace ("[index " str+ (Fin.show i) str+ "] " str+ "last " str+ (ℕ.show target) str+ " " str+ (ℕ.show size)) $ optionalFin target size
    generate' target (i ∷ ind') = trace ("concat " str+ (ℕ.show $ List.length concatted)) concatted
      where
        size = trace ("[index " str+ (Fin.show i) str+ "]") SizedThing.size $ VecAll.lookup i bounds
        candidates = List.allFin size
        usefulCandidates = List.takeWhile ((_≤? target) ∘ toℕ) candidates

        generateChildren : Fin size → _
        generateChildren c = List.map (λ d → c ∷ d) (trace ("child " str+ (Fin.show c) str+ " has " str+ (ℕ.show $ List.length children)) children)
          where children = generate' (target ∸ (toℕ c)) ind'

        nestedLists = trace ("[index " str+ (Fin.show i) str+ "] " str+ "useful " str+ (ℕ.show $ List.length usefulCandidates)) $ List.map generateChildren usefulCandidates
        concatted = trace ("[index " str+ (Fin.show i) str+ "] " str+ "nested " str+ (ℕ.show $ List.length nestedLists)) List.concat nestedLists

sumTermsToString : {n : ℕ} →
                   {things : All (λ _ → SizedThing) (allFin n)} →
                   List (All (λ i → Fin (SizedThing.size (VecAll.lookup i things))) (allFin n)) →
                   String
sumTermsToString [] = "(none)"
sumTermsToString sumTerms = intersperse ",\n" $ List.map (λ st → "[" str+ (intersperse ", " (toList (reduce Fin.show st))) str+ "]") sumTerms

main : Main
main = run do
  -- putStrLn "### 10 with 11"
  -- putStrLn $ sumTermsToString $ sumTerms 10 $ st 11 ∷ []
  -- putStrLn "### 10 with 6,6"
  -- putStrLn $ sumTermsToString $ sumTerms 10 $ st 6 ∷ st 6 ∷ []
  -- putStrLn "### 10 with 7,7"
  -- putStrLn $ sumTermsToString $ sumTerms 10 $ st 7 ∷ st 7 ∷ []
  -- putStrLn "### 10 with 9,7"
  -- putStrLn $ sumTermsToString $ sumTerms 10 $ st 9 ∷ st 7 ∷ []
  -- putStrLn "### 10 with 9,9"
  -- putStrLn $ sumTermsToString $ sumTerms 10 $ st 9 ∷ st 9 ∷ []
  -- putStrLn "### 10 with 11,11"
  -- putStrLn $ sumTermsToString $ sumTerms 10 $ st 11 ∷ st 11 ∷ []
  -- putStrLn "### 10 with 11,11,11"
  -- putStrLn $ sumTermsToString $ sumTerms 10 $ st 11 ∷ st 11 ∷ st 11 ∷ []
  putStrLn "### 10 with Fin 4,4,4"
  putStrLn $ sumTermsToString $ sumTerms 10 $ st 4 ∷ st 4 ∷ st 4 ∷ []
  putStrLn "### 10 with Fin 6,6,6"
  putStrLn $ sumTermsToString $ sumTerms 10 $ st 6 ∷ st 6 ∷ st 6 ∷ []
  putStrLn "### 10 with Fin 6,3,6"
  putStrLn $ sumTermsToString $ sumTerms 10 $ st 6 ∷ st 3 ∷ st 6 ∷ []

