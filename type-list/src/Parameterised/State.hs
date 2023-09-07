{-# LANGUAGE QualifiedDo #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# OPTIONS_GHC -Wno-missing-signatures #-}

module Parameterised.State where

import Data.Kind
import GHC.Types
import Utils
import qualified Utils as Ix
import Prelude hiding (Monad (..))
import GHC.TypeLits
import Data.Proxy
import Unsafe.Coerce

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

type Token :: Type -> Ix.Nat -> Type
newtype Token t n = Token ()

data Future a = Future

put a b = Impure (OHere $ Put a b) pure

alloc a = Impure (OHere $ Alloc a) pure

get a = Impure (OHere $ Get a) pure

fork s = Scope (Fork s) pure

finish s = Scope (Finish s) pure

data StateA p q a where
  PutA :: x -> StateA p x ()
  GetA :: StateA p p p

putAI :: forall p ind effs g ps qs .
  (KnownNat ind, FindEff StateA effs ~ ind, Write ind p ps ~ qs, Assume ind qs ~ p) =>
  p -> IProg effs g ps qs ()
putAI p = Impure (inj (Proxy :: Proxy ind) $ PutA p) pure

getAI :: forall ind effs g ps qs p .
  (KnownNat ind, FindEff StateA effs ~ ind, Assume ind ps ~ p) =>
  IProg effs g ps qs p
getAI = Impure (inj (Proxy :: Proxy ind) GetA) pure

-- stateChangeExp :: forall ind p j effs ps qs sr p1 .
--   ( KnownNat ind
--   , FindEff StateA effs ~ ind
--   , ind                 ~ 0
--   , Assume ind ps       ~ String
--   , Write ind Int ps    ~ qs
--   , qs ~ (Int: sr)
--   ) =>
--   IProg effs StateAG ps qs String
-- -- stateChangeExp :: IProg '[StateA] StateAG '[String] '[Int] String
-- stateChangeExp = Ix.do
--   s <- getAI
--   putAI (5 :: Int)
--   (i :: Int) <- getAI
--   localAG' (+ (1 :: Int)) $ Ix.return ()
--   Ix.return $ s ++ show i


localAG' ::
  (p -> p') ->
  IProg f StateAG (p' : sr1) (q : sr2) a ->
  IProg f StateAG (p : sr1) (p : sr2) a
localAG' f act = Scope (LocalAG f act) pure

data StateAG m p p' q' q x x' where
  LocalAG :: (p -> p') ->
    m (p': sr1) (q: sr2) x -> StateAG m (p: sr1) (p': sr1) (q': sr2) (p: sr2) x x

runStateDirect ::
  p ->
  IProg (StateA:eff) StateAG (p: sr1) (q: sr2) a ->
  IProg eff IVoid sr1 sr2 (a, q)
runStateDirect p (Pure x) = Ix.return (x, p)
runStateDirect p (Impure (OHere GetA) k) =
  runStateDirect p (runIKleisli k p)
runStateDirect _ (Impure (OHere (PutA q)) k) =
  runStateDirect q (runIKleisli k ())
runStateDirect p (Impure (OThere op) k) =
  Impure op $ IKleisliTupled $ \x -> runStateDirect p (runIKleisli k x)
runStateDirect p (Scope (LocalAG f m) k) = Ix.do
  (x, _q) <- runStateDirect (f p) m
  runStateDirect p (runIKleisli k x)

runStateAI ::
  p ->
  IProg (StateA:eff) IVoid (p: sr1) (q: sr2) a ->
  IProg eff IVoid sr1 sr2 (a, q)
runStateAI p (Pure x) = Ix.return (x, p)
runStateAI p (Impure (OHere GetA) k) =
  runStateAI p (runIKleisli k p)
runStateAI _ (Impure (OHere (PutA q)) k) =
  runStateAI q (runIKleisli k ())
runStateAI p (Impure (OThere op) k) =
  Impure op $ IKleisliTupled $ \x -> runStateAI p (runIKleisli k x)
runStateAI _p (Scope _ _) = error "GHC is not exhaustive"


genericState ::
  ( FindEff StateA effs ~ ind
  , Write ind Int p ~ q
  ) =>
  IProg effs g p q ()
genericState = undefined

-- putA ::
--   ( SMember StateA () q effs ps qs
--   ) =>
--   q ->
--   IProg effs g ps qs ()
-- putA q = Impure (inj (PutA q) :: Op effs ps qs ()) pure
