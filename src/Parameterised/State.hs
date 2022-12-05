{-# LANGUAGE AllowAmbiguousTypes #-}
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

type Token :: Type -> Ix.Nat -> Type
newtype Token t n = Token ()

data Future a = Future

put a b = Impure (OHere $ Put a b) emptyCont

alloc a = Impure (OHere $ Alloc a) emptyCont

get a = Impure (OHere $ Get a) emptyCont

fork s = ScopeT (Fork s) emptyCont

finish s = ScopeT (Finish s) emptyCont

data StateA p q a where
  PutA :: x -> StateA p x ()
  GetA :: StateA p p p

putAI ::
  p ->
  MiniEff effs StateA g q p ()
putAI p = ImpureT (PutA p) emptyCont

getAI ::
  MiniEff effs StateA g p p p
getAI = ImpureT (GetA) emptyCont

stateChangeExp ::
  MiniEff effs StateA StateAG String Int String
-- stateChangeExp :: MiniEff '[StateA] StateAG '[String] '[Int] String
stateChangeExp = Ix.do
  s <- getAI
  -- putAI ("Test" :: String)
  putAI (5 :: Int)
  -- putAI (3 :: Int)
  x <- localAG' (+ (1 :: Int)) $ getAI
  Ix.return $ s ++ show x

runStateChangeExp = run $ runStateAIG "Test" stateChangeExp

localAG' ::
  (p -> p') ->
  MiniEff effs f StateAG p' q' a ->
  MiniEff effs f StateAG p p a
localAG' f act = ScopeT (LocalAG f act) emptyCont

data StateAG m p p' q' q x x' where
  LocalAG ::
    (p -> p') ->
    m p' q' x ->
    StateAG m p p' q' p x x

runStateAIG ::
  p ->
  MiniEff eff StateA StateAG p q a ->
  MiniEff eff IIdentity IVoid () () (a, q)
runStateAIG p (Value x) = Ix.return (x, p)
runStateAIG p (Impure cmd k) = Impure cmd $ IKleisliTupled $ \x -> runStateAIG p $ runIKleisliTupled k x
runStateAIG p (ImpureT GetA k) =
  runStateAIG p (runIKleisliTupled k p)
runStateAIG _ (ImpureT (PutA q) k) =
  runStateAIG q (runIKleisliTupled k ())
runStateAIG p (ScopeT (LocalAG f m) k) = Ix.do
  (x, _q) <- runStateAIG (f p) m
  runStateAIG p (runIKleisliTupled k x)

runStateAI ::
  p ->
  MiniEff eff StateA IVoid p q a ->
  MiniEff eff IIdentity IVoid () () (a, q)
runStateAI p (Value x) = Ix.return (x, p)
runStateAI p (Impure cmd k) = Impure cmd $ IKleisliTupled $ \x -> runStateAI p $ runIKleisliTupled k x
runStateAI p (ImpureT GetA k) =
  runStateAI p (runIKleisliTupled k p)
runStateAI _ (ImpureT (PutA q) k) =
  runStateAI q (runIKleisliTupled k ())
runStateAI _p (ScopeT _ _) = error "GHC is not exhaustive"

genericState ::
  MiniEff effs f g p q ()
genericState = undefined

-- putA ::
--   ( Member StateA () q effs ps qs
--   ) =>
--   q ->
--   MiniEff effs g ps qs ()
-- putA q = Impure (inj (PutA q) :: Op effs ps qs ()) emptyCont
