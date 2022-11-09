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

data StateG m p p' q' q x x' where
  Fork :: (AcceptableList p1 q1 p2) => m p2 q2 a -> StateG m p1 p2 q2 q1 a (Future a)
  Finish :: m p2 q2 a -> StateG m p p q p a a

type Token :: Type -> Nat -> Type
newtype Token t n = Token ()

data Future a = Future

put a b = Impure (Put a b) emptyCont

alloc a = Impure (Alloc a) emptyCont

get a = Impure (Get a) emptyCont

fork s = Scope (Fork s) emptyCont

finish s = Scope (Finish s) emptyCont

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

getAI2 :: IProg (f :+: StateA :+: eff) g '(sl, '(p, sr)) '(sl, '(p, sr)) p
getAI2 = Impure (OInr $ OInl GetA) emptyCont

-- putAI2 :: IProg (f :+: StateA :+: eff) g '(sl, '(p, sr)) '(sl, '(p, sr)) p
putAI2 ::
  p
  -> IProg (f1 :+: (StateA :+: f2)) g '(sl, '(q, sr)) '(sl, '(p, sr)) ()
putAI2 x = Impure (OInr $ OInl $ PutA x) emptyCont

stateCIExp :: IProg (StateA :+: StateA :+: eff) StateAG '(String, '((), ())) '(Int, '(String, ())) ()
stateCIExp = Ix.do
  s <- getAI
  _val <- localAG' (const $ Just "") $ Ix.do
    putAI2 "String"
    getAI
  putAI (read s + 100)

runStateAIG ::
  p ->
  IProg (StateA :+: eff) StateAG '(p, sr1) '(q, sr2) a ->
  IProg eff IVoid sr1 sr2 (a, q)
runStateAIG p (Pure x) = Ix.return (x, p)
runStateAIG p (Impure (OInl GetA) k) =
  runStateAIG p (runIKleisliTupled k p)
runStateAIG _ (Impure (OInl (PutA q)) k) =
  runStateAIG q (runIKleisliTupled k ())
runStateAIG p (Impure (OInr op) k) =
  Impure op $ IKleisliTupled $ \x -> runStateAIG p (runIKleisliTupled k x)
runStateAIG p (Scope (LocalAG f m) k) = Ix.do
  (x, _q) <- runStateAIG (f p) m
  runStateAIG p (runIKleisliTupled k x)

runStateAI ::
  p ->
  IProg (StateA :+: eff) IVoid '(p, sr1) '(q, sr2) a ->
  IProg eff IVoid sr1 sr2 (a, q)
runStateAI p (Pure x) = Ix.return (x, p)
runStateAI p (Impure (OInl GetA) k) =
  runStateAI p (runIKleisliTupled k p)
runStateAI _ (Impure (OInl (PutA q)) k) =
  runStateAI q (runIKleisliTupled k ())
runStateAI p (Impure (OInr op) k) =
  Impure op $ IKleisliTupled $ \x -> runStateAI p (runIKleisliTupled k x)
runStateAI _p (Scope _ _) = error "GHC is not exhaustive"

localAG' ::
  (p1 -> p2)
  -> IProg (StateA :+: f) StateAG '(p2, sr1) '(q2, sr2) a
  -> IProg (StateA :+: f) StateAG '(p1, sr1) '(p1, sr2) a
localAG' f act = Scope (LocalAG f act) emptyCont

type StateAG :: forall k.
  (k -> k -> Type -> Type) ->
  k -> k -> k -> k -> Type -> Type -> Type
data StateAG m p p' q' q x x' where
  LocalAG :: (p -> p') ->
    m '(p', sr1) '(q', sr2) x -> StateAG m '(p, sr1) '(p', sr1) '(q', sr2) '(p, sr2) x x