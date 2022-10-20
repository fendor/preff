{-# LANGUAGE GADTs #-}
{-# LANGUAGE RebindableSyntax #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE DataKinds #-}

module Simple.State where

import Utils
import Prelude hiding (Monad (..))
import Data.WorldPeace
import Data.Functor.Identity

data StateS s p q x where
  PutS :: s -> StateS s p q ()
  GetS :: StateS s p q s

data StateG s p p' q' q x' x where
  LocalG :: (s -> s) -> StateG s p p' q' q x x

getS :: IProg (StateS s) g p q s
getS = Impure GetS return

putS :: s -> IProg (StateS s) g p q ()
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

stateExample :: IProg (StateS Int) (StateG Int) p q String
stateExample = do
  i <- getS
  putS (i + i)
  return $ show i

stateWithLocal :: IProg (StateS Int) (StateG Int) p q String
stateWithLocal = do
  n <- getS @Int
  x <- localG (+ n) stateExample
  return $ x ++ ", initial: " ++ show n

ambiguityExample :: IProg (StateS Int) a p q ()
ambiguityExample = do
  _i <- getS
  return ()

typeExperiment :: IProg (StateS Int :+: StateS String :+: IIdentity) k p q String
typeExperiment = undefined

-- runStateE :: s -> IProg (Union IIdentity (StateS s : effs)) k p q a -> IProg (Union IIdentity effs) k p q (s, a)
-- runStateE s (Pure a) = return (s, a)
-- runStateE s (Impure union k) = undefined
-- runStateE s (Scope op prog k) = undefined
-- runStateE s (Impure (Inl GetS) k) = runStateE s undefined -- (k s)
-- runStateE _s (Impure (Inl (PutS s')) k) = Impure undefined res
--   where
--     res = \x -> runStateE s' (k x)
-- runStateE s (Impure (Inr other) k) = Impure other (\x -> runStateE s (k x)) -- (runStateE s (k ()))
-- runStateE s (Scope _ _ _) = undefined
