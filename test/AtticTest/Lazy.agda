-- A program to test when fields are evaluated.
-- They are evaluated lazily.

{-# OPTIONS --guardedness --sized-types --rewriting #-}

module AtticTest.Lazy where

open import Data.Nat
open import Data.Nat.Show
open import Data.String hiding (show)
open import Data.Unit
open import Function using (_$_)
open import IO

open import Debug.Trace using (trace)

record MyRecord : Set where
  field
    approximateSize : ℕ
    computeApproximateSize : ⊤ → ℕ

rec1 : MyRecord
rec1 = record { approximateSize = trace "immediate1" 5 ; computeApproximateSize = λ _ → trace "compute1" 42 }

rec2 : MyRecord
rec2 = record { approximateSize = trace "immediate2" (MyRecord.approximateSize rec1) ; computeApproximateSize = λ _ → trace "compute2" ((MyRecord.computeApproximateSize rec1) _) }

main : Main
main = run $ do
  putStrLn "Doing it 2..."
  putStrLn $ show $ (MyRecord.approximateSize rec2)
  putStrLn $ show $ ((MyRecord.computeApproximateSize rec2) _)
  putStrLn "Doing it 1..."
  putStrLn $ show $ (MyRecord.approximateSize rec1)
  putStrLn $ show $ ((MyRecord.computeApproximateSize rec1) _)
