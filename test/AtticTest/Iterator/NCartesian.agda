{-# OPTIONS --guardedness --sized-types #-}

module AtticTest.Iterator.NCartesian where

open import Attic.Iterator.Base hiding (_∷_)
open import Attic.Iterator.Bound
open import Attic.Iterator.Cartesian

open import Data.List as List using (List; []; _∷_; length; head)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ)
open import Data.Nat.Show using (show)
open import Data.String as Str using (String; intersperse)
open import Data.Product using (_×_; _,_)
open import Data.Vec using (Vec; _∷_; []; allFin; lookup)
open import Data.Vec.Relation.Unary.All using (_∷_; []) renaming (All to VecAll)
open import Function using (_$_; id)
open import IO
import Level
open import Relation.Binary.PropositionalEquality

productItemToString : (String × ℕ × String) → String
productItemToString (s , n , s2) = "(" Str.++ s Str.++ ", " Str.++ (show n) Str.++ ", " Str.++ s2 Str.++ ")"

ℕproductItemToString : (ℕ × ℕ × ℕ) → String
ℕproductItemToString (s , n , s2) = "(" Str.++ (show s) Str.++ ", " Str.++ (show n) Str.++ ", " Str.++ (show s2) Str.++ ")"

module Cube where
  sABC = fromList $ "A" ∷ "B" ∷ "C" ∷ []
  s123 = fromList $  1  ∷  2  ∷  3  ∷ []
  sxyz = fromList $ "x" ∷ "y" ∷ "z" ∷ []
  product = cartesian₃ sABC s123 sxyz

  pl = toList product (bound′ 0 product)

  outMsg = "Count: " Str.++ (show (length pl)) Str.++ "\n" Str.++ (intersperse ",\n" $ List.map productItemToString pl)

main : Main
main = run $ do
  putStrLn "Cube:"
  putStrLn Cube.outMsg
