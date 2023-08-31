{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE QualifiedDo #-}
{-# OPTIONS_GHC -Wno-missing-signatures #-}

module PrEff.Parameterised.State where

import qualified Control.IxMonad as Ix
import Data.Kind
import PrEff (interpretStatefulScoped)
import PrEff hiding (interpretStatefulScoped)
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

data instance ScopeE StateF m p p' q' q x x' where
  Fork :: (AcceptableList p1 q1 p2) => m p2 q2 a -> ScopeE StateF m p1 p2 q2 q1 a (Future a)
  Finish :: m p2 q2 a -> ScopeE StateF m p p q p a a

type Token :: Type -> PrEff.Nat -> Type
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

data instance ScopeE StateP m p p' q' q x x' where
  Zoom ::
    (p -> p') ->
    (q' -> q) ->
    m p' q' x ->
    ScopeE StateP m p p' q' q x x

putAI ::
  p ->
  PrEff effs StateP q p ()
putAI p = sendP (PutP p)

getAI ::
  PrEff effs StateP p p p
getAI = ImpureP (GetP) emptyCont

stateChangeExp ::
  PrEff effs StateP String Int String
stateChangeExp = Ix.do
  s <- getAI
  -- putAI ("Test" :: String)
  putAI (5 :: Int)
  -- putAI (3 :: Int)
  x <- modify (+ (1 :: Int)) $ getAI
  pure $ s ++ show x

runStateChangeExp :: (String, Int)
runStateChangeExp = run $ runStateP "Test Now" stateChangeExp

-- >>> runStateChangeExp
-- ("Test Now6",6)

zoom ::
  (p -> p') ->
  (q' -> q) ->
  PrEff effs StateP p' q' a ->
  PrEff effs StateP p q a
zoom f restore act = ScopedP (Zoom f restore act) emptyCont

modify ::
  (p -> p') ->
  PrEff effs StateP p' q' a ->
  PrEff effs StateP p q' a
modify f act = ScopedP (Zoom f id act) emptyCont

instance ScopedEffect StateP where
  mapS ctx transform (Zoom f restore op) =
    Zoom f restore (transform $ op <$ ctx)

stateAlg :: p -> StateP p q a -> (q, a)
stateAlg k = \case
  GetP -> (k, k)
  PutP q -> (q, ())

runStateDirect ::
  (forall p' q' x. p' -> StateP p' q' x -> (q', x)) ->
  p ->
  PrEff eff StateP p q a ->
  PrEff eff IVoid () () (a, q)
runStateDirect alg p (Value x) = Ix.return (x, p)
runStateDirect alg p (Impure cmd k) =
  Impure cmd
    $ IKleisliTupled
    $ \x -> runStateDirect alg p $ runIKleisliTupled k x
runStateDirect alg p (ImpureP op k) = do
  let (q, a) = stateAlg p op
  runStateDirect alg q (runIKleisliTupled k a)
runStateDirect alg p (ScopedP (Zoom f restore m) k) = Ix.do
  (x, q) <- runStateDirect alg (f p) m
  runStateDirect alg (restore q) (runIKleisliTupled k x)

runStateP ::
  p ->
  PrEff f StateP p q a ->
  PrEff f IVoid () () (a, q)
runStateP =
  interpretStatefulScoped
    ( \s -> \case
        PutP s' -> pure (s', ())
        GetP -> pure (s, s)
    )
    ( \k runner s -> \case
        Zoom f restore m -> Ix.do
          (x, q) <- runner (f s) m
          runner (restore q) $ runIKleisliTupled k x
    )

-- >>>
