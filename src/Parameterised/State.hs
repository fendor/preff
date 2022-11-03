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

put a b = Impure (Put a b) return

alloc a = Impure (Alloc a) return

get a = Impure (Get a) return

fork s = Scope Fork s return

finish s = Scope Finish s return

data StateA p q a where
  PutA :: x -> StateA p x ()
  GetA :: StateA p p p

putA a = Op (Inl $ PutA a) (IKleisliTupled return)

getA = Op (Inl GetA) (IKleisliTupled return)

stateCExp :: Sem (StateA :+: eff) '(String, ()) '(Int, ()) ()
stateCExp = Ix.do
  s <- getA
  putA (read s + 100)

runStateA ::
  p ->
  Sem (StateA :+: eff) '(p, sr1) '(q, sr2) a ->
  Sem eff sr1 sr2 (a, q)
runStateA p (Value x) = Ix.return (x, p)
runStateA p (Op (Inl GetA) k) =
  runStateA p (runIKleisliTupled k p)
runStateA _ (Op (Inl (PutA q)) k) =
  runStateA q (runIKleisliTupled k ())
runStateA p (Op (Inr cmd) k) =
  Op cmd $ IKleisliTupled $ \x -> runStateA p (runIKleisliTupled k x)
