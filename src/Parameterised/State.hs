{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE QualifiedDo #-}
{-# OPTIONS_GHC -Wno-missing-signatures #-}

module Parameterised.State where

import Data.Kind
import MiniEff
import qualified Control.IxMonad as Ix
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

data instance ScopeT StateF m p p' q' q x x' where
  Fork :: (AcceptableList p1 q1 p2) => m p2 q2 a -> ScopeT StateF m p1 p2 q2 q1 a (Future a)
  Finish :: m p2 q2 a -> ScopeT StateF m p p q p a a

type Token :: Type -> MiniEff.Nat -> Type
newtype Token t n = Token ()

data Future a = Future

put a b = Impure (OHere $ Put a b) emptyCont

alloc a = Impure (OHere $ Alloc a) emptyCont

get a = Impure (OHere $ Get a) emptyCont

fork s = ScopedP (Fork s) emptyCont

finish s = ScopedP (Finish s) emptyCont

data StateP p q a where
  PutP :: x -> StateP p x ()
  GetP :: StateP p p p

putAI ::
  p ->
  MiniEff effs StateP q p ()
putAI p = ImpureP (PutP p) emptyCont

getAI ::
  MiniEff effs StateP p p p
getAI = ImpureP (GetP) emptyCont

stateChangeExp ::
  MiniEff effs StateP String Int String
-- stateChangeExp :: MiniEff '[StateA] StateAG '[String] '[Int] String
stateChangeExp = Ix.do
  s <- getAI
  -- putAI ("Test" :: String)
  putAI (5 :: Int)
  -- putAI (3 :: Int)
  x <- modifyP' (+ (1 :: Int)) $ getAI
  Ix.return $ s ++ show x

runStateChangeExp = run $ runStateAIG "Test" stateChangeExp

modifyP' ::
  (p -> p') ->
  MiniEff effs StateP p' q' a ->
  MiniEff effs StateP p p a
modifyP' f act = ScopedP (ModifyP f act) emptyCont

data instance ScopeT StateP m p p' q' q x x' where
  ModifyP ::
    (p -> p') ->
    m p' q' x ->
    ScopeT StateP m p p' q' p x x

instance ScopedEffect StateP where
  mapS ctx transform (ModifyP f op) =
    ModifyP f (transform $ op <$ ctx)

runStateAIG ::
  p ->
  MiniEff eff StateP p q a ->
  MiniEff eff IVoid () () (a, q)
runStateAIG p (Value x) = Ix.return (x, p)
runStateAIG p (Impure cmd k) = Impure cmd $ IKleisliTupled $ \x -> runStateAIG p $ runIKleisliTupled k x
runStateAIG p (ImpureP GetP k) =
  runStateAIG p (runIKleisliTupled k p)
runStateAIG _ (ImpureP (PutP q) k) =
  runStateAIG q (runIKleisliTupled k ())
runStateAIG p (ScopedP (ModifyP f m) k) = Ix.do
  (x, _q) <- runStateAIG (f p) m
  runStateAIG p (runIKleisliTupled k x)

