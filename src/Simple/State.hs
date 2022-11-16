{-# LANGUAGE RebindableSyntax #-}
module Simple.State where

import Utils
import Prelude hiding (Monad (..))

data StateS s p q x where
  PutS :: s -> StateS s p p ()
  GetS :: StateS s p p s

data StateG s m p p' q' q x x' where
  LocalG :: (s -> s) -> m p' q' x -> StateG s m p p' q' q x x

getS :: IProg '[StateS s] g '[p] '[p] s
getS = Impure (OHere GetS) emptyCont

putS :: s -> IProg '[StateS s] g '[p] '[p] ()
putS s = Impure (OHere $ PutS s) emptyCont

localG :: (s -> s) -> IProg f (StateG s) q r a -> IProg f (StateG s) p r a
localG f prog = Scope (LocalG f prog) emptyCont

runStateS :: s -> IProg '[StateS s] (StateG s) p q a -> (s, a)
runStateS s (Pure a) = (s, a)
runStateS s (Impure (OHere GetS) k) = runStateS s (runIKleisliTupled k s)
runStateS _s (Impure (OHere (PutS s')) k) = runStateS s' (runIKleisliTupled k ())
runStateS _s (Impure (OThere _) _k) = error "Inaccessible"
runStateS s (Scope (LocalG f prog) k) = runStateS s (runIKleisliTupled k x)
 where
  (_, x) = runStateS (f s) prog

runState :: s -> IProg '[StateS s] IVoid p q a -> (s, a)
runState s (Pure a) = (s, a)
runState s (Impure (OHere GetS) k) = runState s (runIKleisliTupled k s)
runState _s (Impure (OHere (PutS s')) k) = runState s' (runIKleisliTupled k ())
runState s (Impure (OThere _) _k) = error "Inaccessible"
runState _ (Scope _ _) = error "Impossible, Scope node must never be created"

stateExample :: IProg '[StateS Int] (StateG Int) '[()] '[()] String
stateExample = do
  i <- getS
  putS (i + i)
  return $ show i

stateWithLocal :: IProg '[StateS Int] (StateG Int) '[()] '[()] String
stateWithLocal = do
  n <- getS @Int
  x <- localG (+ n) stateExample
  return $ x ++ ", initial: " ++ show n

ambiguityExample :: IProg '[StateS Int] a '[()] '[()] ()
ambiguityExample = do
  _i <- getS
  return ()
