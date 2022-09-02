module Attic.Tactics.Intro where

open import Attic.BasicTactics
open import Attic.Core
open import Attic.Development
open import Attic.GlobalImports
open import Attic.Macro
open import Attic.Monad
open import Attic.TCTactics

open import Data.Bool using (Bool)
open import Data.Nat using (ℕ)
open import Data.List using (_∷_; [])
open import Data.Product using (_,_)
open import Reflection using (Term; Literal; arg; abs)
open import Reflection.Argument.Information using (visibility)

open Term using (pi; lit; lam; def; unknown; var)
open Literal using (nat)

intro : Attic ⊤
intro = do
  (goal , type) ← getGoalAndType
  pi a@(arg argInfo _) b@(abs paramName returnType) ← reduce type
    where t → do
      failure $ strErr "Expected a function type, got " ∷ termErr t ∷ []
  let paramBinding : Binding
      paramBinding = paramName , a
  body ← newUnknownMetaContext $ paramBinding ∷ Goal.context goal
  meta ← getMeta! body
  let v        = visibility argInfo
      lmbd     = lam v (abs paramName body)
      bodyGoal : Goal
      bodyGoal = (record { type = returnType
                         ; hole = body
                         ; meta = meta
                         ; context = paramBinding ∷ Goal.context goal })
  solveGoal goal lmbd
  addFocusGoal bodyGoal

macro
  intro′ = asMacro $ intro
