module Control.IxMonad where

import Prelude hiding (Monad(..), Applicative(..), Functor(..))
import Data.Kind

-- ------------------------------------------------
-- Parametric Effect monad
-- ------------------------------------------------

type IMonad :: (p -> p -> Type -> Type) -> Constraint
class IMonad m where
  return :: a -> m i i a
  (>>=) :: m i j a -> (a -> m j k b) -> m i k b
  (>>) :: m i j a -> m j k b -> m i k b
  g >> f = g >>= const f

type IFunctor :: (p -> p -> Type -> Type) -> Constraint
class IFunctor f where
  imap :: (a -> b) -> f p q a -> f p q b

  (<$) :: a -> f p q b -> f p q a
  (<$) =  imap . const

class IFunctor f => IApplicative f where
  pure :: a -> f i i a
  (<*>) :: f i j (a -> b) -> f j r a -> f i r b

  (*>) ::
    f i j b1 -> f j r b2 -> f i r b2
  a1 *> a2 = (id <$ a1) <*> a2


-- ------------------------------------------------
-- IMonad utilities
-- ------------------------------------------------

replicateM_ :: IApplicative f => Int -> f p p a -> f p p ()
replicateM_ cnt0 f =
    loop cnt0
  where
    loop cnt
        | cnt <= 0  = pure ()
        | otherwise = f *> loop (cnt - 1)

forM_ :: (IMonad m) => [a] -> (a -> m i i ()) -> m i i ()
forM_ [] _ = return ()
forM_ [x] f =
  f x
forM_ (x : xs) f =
  f x >>= \_c -> forM_ xs f
