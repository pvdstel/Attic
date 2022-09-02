-- A program to test colist

{-# OPTIONS --guardedness --sized-types #-}

module AtticTest.Colist where

open import Codata.Colist using (unfold; take)
open import Data.Bool using (true; false)
open import Data.List using (List; foldr; _∷_; [])
open import Data.Maybe
open import Data.Nat
open import Data.Nat.Show renaming (show to showℕ)
open import Data.Product using (_×_ ; _,_)
open import Data.String using (String) renaming (_++_ to _str++_)
open import Data.Vec as Vec using (toList)
open import Data.Vec.Bounded as Vec≤ using (Vec≤; map; _∷_)
open import IO
open import Relation.Nullary using (Dec)
open import Relation.Nullary.Decidable using (isYes)

nats = unfold f 1
  where
    f : ℕ → Maybe (ℕ × ℕ)
    f i = just ( (suc i) , i )

natsTo50 = unfold f 1
  where
    f : ℕ → Maybe (ℕ × ℕ)
    f i with isYes (i <? 51)
    ...    | true = just ( (suc i) , i )
    ...    | false = nothing

taking = 100
intermediateVector = take taking natsTo50

joinStringByComma : List String → String
joinStringByComma [] = ""
joinStringByComma (s ∷ []) = s
joinStringByComma (s ∷ ss) = s str++ ", " str++ (joinStringByComma ss)

joinVecByComma : ∀ {n} → Vec≤ String n → String
joinVecByComma {n} (vec Vec≤., bound) = joinStringByComma (toList vec)

stringElements = Vec≤.map showℕ intermediateVector
listAsString = joinVecByComma stringElements

outMsg = "The list is " str++ listAsString

main : Main
main = run (putStrLn outMsg)
