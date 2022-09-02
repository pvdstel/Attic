module Attic.TCTactics where

open import Attic.Core
open import Attic.GlobalImports
open import Attic.Monad

open import Data.Bool using (true)
open import Data.List using ([]; _∷_)

import Reflection as TC
open TC using (Definition; Name; Term; Type)

newUnknownMeta : Attic Term
newUnknownMeta = liftTC! $ TC.newMeta TC.unknown

newUnknownMetaContext : Context → Attic Term
newUnknownMetaContext ctx = liftTC! $ TC.inContext (contextToTCContext ctx) $ TC.newMeta TC.unknown

reduce : Term → Attic Term
reduce t = liftTC! $ TC.reduce t

quoteTC : ∀ {a} {A : Set a} → A → Attic Term
quoteTC t = liftTC! $ TC.quoteTC t

quoteNormalisedTC : ∀ {a} {A : Set a} → A → Attic Term
quoteNormalisedTC t = liftTC! $ TC.withNormalisation true $ TC.quoteTC t

getDefinition : Name → Attic Definition
getDefinition name = liftTC! $ TC.getDefinition name

getType : Name → Attic Type
getType n = liftTC! $ TC.getType n
