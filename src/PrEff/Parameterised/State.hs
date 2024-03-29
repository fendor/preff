{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE QualifiedDo #-}
{-# OPTIONS_GHC -Wno-missing-signatures #-}
{-# LANGUAGE BlockArguments #-}

module PrEff.Parameterised.State where

import qualified Control.IxMonad as Ix
import PrEff (interpretStatefulScoped)
import PrEff hiding (interpretStatefulScoped)
import Prelude hiding (Monad (..))


data StateP p q a where
  PutP :: x -> StateP p x ()
  GetP :: StateP p p p

data instance ScopeE StateP m p p' q' q x x' where
  ZoomP ::
    (p -> p') ->
    (q' -> q) ->
    m p' q' x ->
    ScopeE StateP m p p' q' q x x

instance ScopedEffect StateP where
  weave ctx transform (ZoomP f restore op) =
    ZoomP f restore (transform $ op <$ ctx)

putP ::
  p ->
  PrEff effs StateP q p ()
putP p = sendP (PutP p)

getP ::
  PrEff effs StateP p p p
getP = sendP GetP

zoomP ::
  (p -> p') ->
  (q' -> q) ->
  PrEff effs StateP p' q' a ->
  PrEff effs StateP p q a
zoomP f restore act = sendScoped (ZoomP f restore act)

modifyP ::
  (p -> p') ->
  PrEff effs StateP p' q' a ->
  PrEff effs StateP p q' a
modifyP f act = sendScoped (ZoomP f id act)

stateChangeExp ::
  PrEff effs StateP String Int String
stateChangeExp = Ix.do
  s <- getP
  putP (5 :: Int)
  x <- zoomP (+ (1 :: Int)) id $ getP
  pure $ s ++ show x

runStateChangeExp :: (String, Int)
runStateChangeExp = run $ runStateP "Test Now" stateChangeExp

-- >>> runStateChangeExp
-- ("Test Now6",6)


stateAlg :: p -> StateP p q a -> (q, a)
stateAlg k = \case
  GetP -> (k, k)
  PutP q -> (q, ())

runStateP ::
  p ->
  PrEff f StateP p q a ->
  PrEff f IVoid () () (a, q)
runStateP =
  interpretStatefulScopedH
    do \s -> \case
        PutP s' -> pure (s', ())
        GetP -> pure (s, s)

    do \run s -> \case
        ZoomP f restore act -> do
          (x, q) <- run (f s) act
          pure (x, restore q)

runStateP' ::
  p ->
  PrEff f StateP p q a ->
  PrEff f IVoid () () (q, a)
runStateP' p = \case
  Value x -> pure (p, x)
  Impure op k ->
    Impure op (\x -> runStateP' p (k x))
  ImpureP op k -> case op of
    PutP x -> runStateP' x (k ())
    GetP -> runStateP' p (k p)
  ScopedP op k -> case op of
    ZoomP f restore act -> do
      (q', a) <- runStateP' (f p) act
      runStateP' (restore q') (k a)

runStateP'' ::
  p ->
  PrEff f StateP p q a ->
  PrEff f IVoid () () (a, q)
runStateP'' =
  interpretStatefulScoped
    do \s -> \case
        PutP s' -> pure (s', ())
        GetP -> pure (s, s)

    do \continue run s -> \case
        ZoomP f restore act -> do
          (x, q) <- run (f s) act
          run (restore q) $ continue  x
