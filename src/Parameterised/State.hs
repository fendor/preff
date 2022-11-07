{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE QualifiedDo #-}
{-# OPTIONS_GHC -Wno-missing-signatures #-}

module Parameterised.State where

import Data.Kind
import Utils
import qualified Utils as Ix
import Prelude hiding (Monad (..))

data StateF p q x where
  Alloc :: t -> StateF p (Append p X) (Token t (Length p))
  Get ::
    (R ≤ Lookup p n) =>
    Token t n ->
    StateF p p t
  Put ::
    (X ≤ Lookup p n) =>
    Token t n ->
    t ->
    StateF p p ()

data StateG p p' q' q x x' where
  Fork :: (AcceptableList p1 q1 p2) => StateG p1 p2 q2 q1 a (Future a)
  Finish :: StateG p p q p a a

type Token :: Type -> Nat -> Type
newtype Token t n = Token ()

data Future a = Future

put a b = Impure (Put a b) emptyCont

alloc a = Impure (Alloc a) emptyCont

get a = Impure (Get a) emptyCont

fork s = Scope Fork s return

finish s = Scope Finish s return

data StateA p q a where
  PutA :: x -> StateA p x ()
  GetA :: StateA p p p

putA a = Op (OInl $ PutA a) emptyCont

getA = Op (OInl GetA) emptyCont

stateCExp :: Sem (StateA :+: eff) '(String, ()) '(Int, ()) ()
stateCExp = Ix.do
  s <- getA
  putA (read s + 100)

runStateA ::
  p ->
  Sem (StateA :+: eff) '(p, sr1) '(q, sr2) a ->
  Sem eff sr1 sr2 (a, q)
runStateA p (Value x) = Ix.return (x, p)
runStateA p (Op (OInl GetA) k) =
  runStateA p (runIKleisliTupled k p)
runStateA _ (Op (OInl (PutA q)) k) =
  runStateA q (runIKleisliTupled k ())
runStateA p (Op (OInr cmd) k) =
  Op cmd $ IKleisliTupled $ \x -> runStateA p (runIKleisliTupled k x)

putAI :: p -> IProg (StateA :+: eff) g '(q, sr) '(p, sr) ()
putAI p = Impure (OInl $ PutA p) emptyCont

getAI :: IProg (StateA :+: eff) g '(p, sr) '(p, sr) p
getAI = Impure (OInl GetA) emptyCont

stateCIExp :: IProg (StateA :+: eff) p '(String, ()) '(Int, ()) ()
stateCIExp = Ix.do
  s <- getAI
  putAI (read s + 100)

runStateAI ::
  
  p ->
  IProg (StateA :+: eff) (StateAG :++: effG) '(p, sr1) '(q, sr2) a ->
  IProg eff effG sr1 sr2 (a, q)
runStateAI p (Pure x) = Ix.return (x, p)
runStateAI p (Impure (OInl GetA) k) =
  runStateAI p (runIKleisliTupled k p)
runStateAI _ (Impure (OInl (PutA q)) k) =
  runStateAI q (runIKleisliTupled k ())
runStateAI p (Impure (OInr op) k) =
  Impure op $ IKleisliTupled $ \x -> runStateAI p (runIKleisliTupled k x)
runStateAI p (Scope (SInl (LocalAG f)) act k) = Ix.do
  (x, p') <- runStateAI (f p) act
  runStateAI p' (k x)
runStateAI p (Scope (SInr op) act k) = Ix.do
  -- TODO: weave abstraction
  let act' = Ix.iweave undefined undefined undefined
  Scope op act' $ IKleisliTupled $ \x -> runStateAI p (runIKleisliTupled k x)


type StateAG :: forall k.
  k -> k -> k -> k -> Type -> Type -> Type
data StateAG p p' q' q x x' where
  LocalAG :: (p -> p') ->
    StateAG p p' q q x x

