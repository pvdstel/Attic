module Attic.Tactics.Constructor where

open import Attic.BasicTactics
open import Attic.Core
open import Attic.Development
open import Attic.GlobalImports
open import Attic.Iterator as Iterator using (map-syntax)
open import Attic.Monad
open import Attic.TCTactics
open import Attic.Utils.Reflection using (makeArgImplicit)

open import Data.Nat using (ℕ)
open import Data.List as List using (List; []; [_]; _∷_)
open import Data.Product using (_×_; _,_; _,′_; map₁)
open import Function using (flip)
open import Level using (Level)
open import Reflection using (Arg; Name; Term; Type)

open Term using (con; def)

private
  noDataOrRecord : ∀ {a} {A : Set a} → Term → Attic A {Level.zero}
  noDataOrRecord t = failure $ strErr "The type is not a data type or record: " ∷ termErr t ∷ []

  getConstructors : Type → Attic ((List (Arg Term) × ℕ) × List Name) {Level.zero}
  getConstructors t = do
    def tName tArgs ← reduce t
      where
        _ → noDataOrRecord t
    getDefinition tName >>= λ {
        (Reflection.data-type #pars cs) → return ((tArgs , #pars) , cs)
      ; (Reflection.record-type c fs) → return ((tArgs , List.length tArgs) , [ c ])
      ; _ → noDataOrRecord t
      }

  unfoldConstructorType : Type → (Context × Type)
  unfoldConstructorType (Reflection.pi a (Reflection.abs argN tT)) =
    map₁ ((argN , a) ∷_) (unfoldConstructorType tT)
  unfoldConstructorType t = [] , t

  makeGoals : (baseTel : Context) → (params : Context) → Attic (List Goal) {Level.zero}
  makeGoals baseTel [] = return []
  makeGoals baseTel ((_ , Reflection.arg i tParam) ∷ params′) = do
    newHole ← newUnknownMetaContext baseTel
    meta ← getMeta! newHole
    rec ← makeGoals baseTel params′
    let goal = record { type = tParam
                      ; hole = newHole
                      ; meta = meta
                      ; context = baseTel
                      }
    return (goal ∷ rec)

  makeArgs : Context → List Goal → List (Arg Term)
  makeArgs ((_ , Reflection.arg i t) ∷ params′) (goal ∷ goals′) = cur ∷ rec
    where
      cur = Reflection.arg i (Goal.hole goal)
      rec = makeArgs params′ goals′
  makeArgs _ _ = []

introConstructor : Attic ⊤
introConstructor = do
  goal , type ← getGoalAndType
  (tArgs , #tParams) , conNames ← getConstructors type
  let tParams = List.take #tParams tArgs
      implicitTParams = List.map makeArgImplicit tParams
      conNamesIter = Iterator.fromList conNames
      tacticPrograms = for c of conNamesIter ∶ do
        tCon ← getType c
        let (pars , _) = unfoldConstructorType tCon
            valuePars = List.drop #tParams pars
        goals ← makeGoals (Goal.context goal) valuePars
        let conArgs = makeArgs valuePars goals
            solution = con c conArgs
        solveGoal goal solution
        addFocusGoals goals
        debugLogProofState
  branch′ tacticPrograms

constr = introConstructor
