-- Contains some global imports that are useful

module Attic.GlobalImports where

module StdM where
  open import Category.Monad using (RawMonad)
  open RawMonad {{...}} using (return; _>>=_; _>>_) public

  open import Category.Functor using (RawFunctor)
  open RawFunctor {{...}} using (_<$>_) public

open import Data.Maybe using (Maybe; just; nothing) public

open import Data.Unit using (⊤; tt) public

open import Function using (_$_; _∘_) public
