{-# LANGUAGE GADTs #-}
{-# LANGUAGE RebindableSyntax #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE DataKinds #-}

module Simple.State where

import Utils
import Prelude hiding (Monad (..))

data StateS s p q x where
  PutS :: s -> StateS s p p ()
  GetS :: StateS s p p s

data StateG s p p' q' q x' x where
  LocalG :: (s -> s) -> StateG s p p' q' q x x

getS :: IProg (StateS s) g p p s
getS = Impure GetS return

putS :: s -> IProg (StateS s) g p p ()
putS s = Impure (PutS s) return

localG :: (s -> s) -> IProg f (StateG s) q r a -> IProg f (StateG s) p r a
localG f prog = Scope (LocalG f) prog return

runState :: s -> IProg (StateS s) (StateG s) p q a -> (s, a)
runState s (Pure a) = (s, a)
runState s (Impure GetS k) = runState s (k s)
runState _s (Impure (PutS s') k) = runState s' (k ())
runState s (Scope (LocalG f) prog k) = runState s (k x)
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

typeExperiment :: IProg (Op [StateS Int, StateS String]) k p p String
typeExperiment = do
  i <- getNS1 @Int
  putNS2 (show i)
  return "test"

getNS1 :: IProg (Op (StateS i: effs)) k p p i
getNS1 = Impure (Here GetS) return

putNS2 :: i -> IProg (Op (s: StateS i: effs)) k p p ()
putNS2 i = Impure (There (Here $ PutS i)) return

runExp :: (String, (Int, String))
runExp = run $ runStateE "Test" $ runStateE 10 typeExperiment

runStateE :: s -> IProg (Op (StateS s : effs)) k p q a -> IProg (Op effs) k p q (s, a)
runStateE s (Pure a) = Pure (s, a)
runStateE s (Impure (Here GetS) k) = runStateE s (k s)
runStateE _s (Impure (Here (PutS s')) k) = runStateE s' (k ())
runStateE s (Impure (There other) k) = Impure other (\x -> runStateE s (k x)) -- (runStateE s (k ()))
runStateE _s Scope {} = undefined

