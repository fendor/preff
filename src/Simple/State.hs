{-# LANGUAGE RebindableSyntax #-}
module Simple.State where

import Utils
import Prelude hiding (Monad (..))

data StateS s p q x where
  PutS :: s -> StateS s p p ()
  GetS :: StateS s p p s

data StateG s m p p' q' q x x' where
  LocalG :: (s -> s) -> m p' q' x -> StateG s m p p' q' q x x

getS :: IProg (StateS s) g p p s
getS = Impure GetS emptyCont

putS :: s -> IProg (StateS s) g p p ()
putS s = Impure (PutS s) emptyCont

localG :: (s -> s) -> IProg f (StateG s) q r a -> IProg f (StateG s) p r a
localG f prog = Scope (LocalG f prog) emptyCont

runState :: s -> IProg (StateS s) (StateG s) p q a -> (s, a)
runState s (Pure a) = (s, a)
runState s (Impure GetS k) = runState s (runIKleisliTupled k s)
runState _s (Impure (PutS s') k) = runState s' (runIKleisliTupled k ())
runState s (Scope (LocalG f prog) k) = runState s (runIKleisliTupled k x)
 where
  (_, x) = runState (f s) prog

stateExample :: IProg (StateS Int) (StateG Int) p p String
stateExample = do
  i <- getS
  putS (i + i)
  return $ show i

stateWithLocal :: IProg (StateS Int) (StateG Int) p p String
stateWithLocal = do
  n <- getS @Int
  x <- localG (+ n) stateExample
  return $ x ++ ", initial: " ++ show n

ambiguityExample :: IProg (StateS Int) a p p ()
ambiguityExample = do
  _i <- getS
  return ()
