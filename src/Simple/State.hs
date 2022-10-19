{-# LANGUAGE GADTs #-}
{-# LANGUAGE RebindableSyntax #-}
{-# LANGUAGE TypeApplications #-}

module Simple.State where

import Utils
import Prelude hiding (Monad (..))

data StateS s p q x where
  PutS :: s -> StateS s p q ()
  GetS :: StateS s p q s

data StateG s p p' q' q x x' where
  LocalG :: (s -> s) -> StateG s p p' q' q x x

getS :: IProg (StateS s) g p q s
getS = Impure GetS return

putS :: s -> IProg (StateS s) g p q ()
putS s = Impure (PutS s) return

localS :: (s -> s) -> IProg f (StateG s) q r a -> IProg f (StateG s) p r a
localS f prog = Scope (LocalG f) prog return

runState :: s -> IProg (StateS s) (StateG s) p q a -> (s, a)
runState s (Pure a) = (s, a)
runState s (Impure GetS k) = runState s (k s)
runState _s (Impure (PutS s') k) = runState s' (k ())
runState s (Scope (LocalG f) prog k) = runState s (k x)
  where
    (_, x) = runState (f s) prog

stateExample :: IProg (StateS Int) (StateG Int) p q String
stateExample = do
  i <- getS
  putS (i + i)
  return $ show i

stateWithLocal :: IProg (StateS Int) (StateG Int) p q String
stateWithLocal = do
  n <- getS
  x <- localS (+ n) stateExample
  return $ x ++ ", initial: " ++ show n

ambiguityExample :: IProg (StateS Int) a p q ()
ambiguityExample = do
  _i <- getS
  return ()
