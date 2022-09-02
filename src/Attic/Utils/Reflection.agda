module Attic.Utils.Reflection where

open import Data.List using (List; map)
open import Data.Product using (_×_; _,_)
open import Data.String using (String)
open import Function using (_∘_)
open import Level
open import Reflection using (TC; Type; bindTC) renaming (return to returnTC)
open import Reflection.Term using (Telescope)
open import Reflection.Argument using (Arg; arg)
open import Reflection.Argument.Information using (arg-info)
open import Reflection.Argument.Visibility using (hidden)

private
  variable
    x : Level
    X : Set x

fmapTC : ∀ {a b} {A : Set a} {B : Set b} → (A → B) → TC A → TC B
fmapTC = λ f mx → bindTC mx (returnTC ∘ f)

TCBinding = Arg Type
TCContext = List TCBinding
Binding = String × Arg Type
Context = Telescope -- List (String × Arg Type)

thenTC : ∀ {a b} {A : Set a} {B : Set b} → TC A → TC B → TC B
thenTC a b = bindTC a λ _ → b
{-# INLINE thenTC #-}

tcBindingToBinding : TCBinding → Binding
tcBindingToBinding tcBind = "x" , tcBind

tcContextToContext : TCContext → Context
tcContextToContext tcCtx = map tcBindingToBinding tcCtx

bindingToTCBinding : Binding → TCBinding
bindingToTCBinding = Data.Product.proj₂

contextToTCContext : Context → TCContext
contextToTCContext ctx = map bindingToTCBinding ctx

-- Makes an argument implicit
-- From Jesper Cockx's Ataca project
-- This function preserves the data and relevance, but sets the visibility to
-- hidden.
makeArgImplicit : Arg X → Arg X
makeArgImplicit (arg (arg-info v r) x) = arg (arg-info hidden r) x
