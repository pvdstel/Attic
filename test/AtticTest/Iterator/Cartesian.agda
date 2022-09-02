{-# OPTIONS --guardedness --sized-types #-}

module AtticTest.Iterator.Cartesian where

open import Attic.Iterator.Base hiding (_∷_)
open import Attic.Iterator.Bound
open import Attic.Iterator.Cartesian

open import Data.List as List using (List; []; _∷_; length; head)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ)
open import Data.Nat.Show using (show)
open import Data.String as Str using (String; intersperse)
open import Data.Product using (_×_; _,_)
open import Function using (_$_)
open import IO
open import Relation.Binary.PropositionalEquality

productItemToString : (String × ℕ) → String
productItemToString (s , n) = "(" Str.++ s Str.++ ", " Str.++ (show n) Str.++ ")"

module Empty where
  emptyℕ : Iterator ℕ
  emptyℕ = empty
  emptyStr : Iterator String
  emptyStr = empty

  one = fromList $ "A" ∷ "B" ∷ []
  two = fromList $ 0 ∷ 1 ∷ []

  0×0 = cartesian emptyℕ emptyStr
  0×2 = cartesian emptyStr two
  2×0 = cartesian one emptyℕ

  _ : toList 0×0 (bound′ 0 0×0) ≡ []
  _ = refl
  _ : toList 0×2 (bound′ 0 0×2) ≡ []
  _ = refl
  _ : toList 2×0 (bound′ 0 2×0) ≡ []
  _ = refl

module Single where
  one = fromList $ "A" ∷ []
  two = fromList $ 0 ∷ []

  product = cartesian one two

  pl = toList product (bound′ 0 product)

  _ : pl ≡ ("A" , 0) ∷ []
  _ = refl

  outMsg = intersperse ",\n" $ List.map productItemToString pl

module Row where
  one = fromList $ "A" ∷ "B" ∷ "C" ∷ "D" ∷ "E" ∷ "F" ∷ []
  two = fromList $ 0 ∷ []

  product = cartesian one two

  _ : Iterator.bound product ≡ bounded 18
  _ = refl

  pl = toList product (bound′ 0 product)

  _ : pl ≡ ("A" , 0) ∷ ("B" , 0) ∷ ("C" , 0) ∷ ("D" , 0) ∷ ("E" , 0) ∷ ("F" , 0) ∷ []
  _ = refl

  outMsg = intersperse ",\n" $ List.map productItemToString pl

module RowDouble where
  one = fromList $ "A" ∷ "B" ∷ "C" ∷ "D" ∷ "E" ∷ "F" ∷ []
  two = fromList $ 0 ∷ 1 ∷ []

  product = cartesian one two

  _ : Iterator.bound product ≡ bounded 24
  _ = refl

  pl = toList product (bound′ 0 product)

  outMsg = intersperse ",\n" $ List.map productItemToString pl

module Column where
  one = fromList $ "A" ∷ []
  two = fromList $ 0 ∷ 1 ∷ 2 ∷ 3 ∷ 4 ∷ 5 ∷ 6 ∷ []

  product = cartesian one two

  _ : Iterator.bound product ≡ bounded 21
  _ = refl

  pl = toList product (bound′ 0 product)

  _ : pl ≡ ("A" , 0) ∷ ("A" , 1) ∷ ("A" , 2) ∷ ("A" , 3) ∷ ("A" , 4) ∷ ("A" , 5) ∷ ("A" , 6) ∷ []
  _ = refl

  outMsg = intersperse ",\n" $ List.map productItemToString pl

module ColumnDouble where
  one = fromList $ "A" ∷ "B" ∷ []
  two = fromList $ 0 ∷ 1 ∷ 2 ∷ 3 ∷ 4 ∷ 5 ∷ 6 ∷ []

  product = cartesian one two

  _ : Iterator.bound product ≡ bounded 28
  _ = refl

  pl = toList product (bound′ 0 product)

  outMsg = intersperse ",\n" $ List.map productItemToString pl

module Square where
  one = fromList $ "A" ∷ "B" ∷ "C" ∷ []
  two = fromList $ 1 ∷ 2 ∷ 3 ∷ []

  product = cartesian one two

  _ : Iterator.bound product ≡ bounded 15
  _ = refl

  pl = toList product (bound′ 0 product)

  _ : length pl ≡ 9
  _ = refl

  _ : pl ≡ ("A" , 1) ∷ ("A" , 2) ∷ ("B" , 1) ∷
           ("A" , 3) ∷ ("B" , 2) ∷ ("C" , 1) ∷
           ("B" , 3) ∷ ("C" , 2) ∷ ("C" , 3) ∷ []
  _ = refl

  outMsg = intersperse ",\n" $ List.map productItemToString pl

main : Main
main = run $ do
  putStrLn "Single:"
  putStrLn Single.outMsg
  putStrLn "------\nRow:"
  putStrLn Row.outMsg
  putStrLn "------\nRowDouble:"
  putStrLn RowDouble.outMsg
  putStrLn "------\nColumn:"
  putStrLn Column.outMsg
  putStrLn "------\nColumnDouble:"
  putStrLn ColumnDouble.outMsg
  putStrLn "------\nSquare:"
  putStrLn Square.outMsg
