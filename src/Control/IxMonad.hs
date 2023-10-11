{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -Wno-orphans #-}
module Control.IxMonad where

import Data.Kind
import Prelude hiding (Applicative (..), Functor (..), Monad (..), mapM, (=<<))
import qualified Prelude as P

-- ------------------------------------------------
-- Parametric indexed monad
-- ------------------------------------------------

type IMonad :: (p -> p -> Type -> Type) -> Constraint
class IApplicative m => IMonad m where
  return :: a -> m i i a
  (>>=) :: m i j a -> (a -> m j k b) -> m i k b
  (>>) :: m i j a -> m j k b -> m i k b
  g >> f = g >>= const f

  return = pure

join :: IMonad m => m i j (m j k a) -> m i k a
join m = m >>= id

(=<<) :: IMonad m => (a -> m j k b) -> m i j a -> m i k b
f =<< m = m >>= f

(>=>) :: IMonad m => (a -> m i j b) -> (b -> m j k c) -> (a -> m i k c)
f >=> g = \a -> (f a >>= g)

(<=<) :: IMonad m => (b -> m j k c) -> (a -> m i j b) -> (a -> m i k c)
f <=< g = \a -> (f =<< g a)

type IFunctor :: (p -> p -> Type -> Type) -> Constraint
class IFunctor f where
  imap :: (a -> b) -> f p q a -> f p q b

  (<$) :: a -> f p q b -> f p q a
  (<$) = imap . const

class (IFunctor f) => IApplicative f where
  pure :: a -> f i i a
  (<*>) :: f i j (a -> b) -> f j r a -> f i r b

  (*>) ::
    f i j b1 -> f j r b2 -> f i r b2
  a1 *> a2 = (id <$ a1) <*> a2

instance IFunctor m => P.Functor (m p q) where
  fmap = imap

instance IApplicative m => P.Applicative (m p p) where
  pure = pure
  (<*>) = (<*>)

instance IMonad m => P.Monad (m p p) where
  (>>=) = (>>=)

-- ------------------------------------------------
-- Rebindable Syntax and IMonad Utils
-- ------------------------------------------------

ifThenElse :: Bool -> p -> p -> p
ifThenElse True a _ = a
ifThenElse False _ b = b

when :: IMonad m => Bool -> m i i () -> m i i ()
when False _ = pure ()
when True a = a

foldM :: IMonad m => [a] -> c -> (a -> c -> m i i c) -> m i i c
foldM [] c _f = return c
foldM [x] c f =
  f x c
foldM (x : xs) c f =
  f x c >>= \c' -> foldM xs c' f

replicateM_ :: (IApplicative f) => Int -> f p p a -> f p p ()
replicateM_ cnt0 f =
  loop cnt0
 where
  loop cnt
    | cnt <= 0 = pure ()
    | otherwise = f *> loop (cnt - 1)

replicateM :: (IApplicative f) => Int -> f p p a -> f p p [a]
replicateM cnt0 f =
  loop cnt0
 where
  loop cnt
    | cnt <= 0 = pure []
    | otherwise = (imap (\x -> \xs -> (x : xs)) f) <*> loop (cnt - 1)

forM :: (IMonad m) => [a] -> (a -> m i i b) -> m i i [b]
forM [] _ = pure []
forM [x] f = Control.IxMonad.do
  c <- f x
  pure [c]
forM (x : xs) f = Control.IxMonad.do
  c <- f x
  cs <- forM xs f
  pure (c : cs)

forM_ :: (IMonad m) => [a] -> (a -> m i i ()) -> m i i ()
forM_ xs f = Control.IxMonad.do
  _ <- forM xs f
  pure ()

mapM :: (IMonad m) => (a -> m p p b) -> [a] -> m p p [b]
mapM _ [] = return []
mapM f (x : xs) =
  f x >>= \c -> imap (c :) $ mapM f xs

mapM_ :: (IMonad m) => (a -> m p p b) -> [a] -> m p p ()
mapM_ f xs = Control.IxMonad.do
  _ <- mapM f xs
  pure ()
