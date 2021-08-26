{-# OPTIONS_GHC -fplugin=Plugin #-}

{-# LANGUAGE BlockArguments, DataKinds, LambdaCase, FlexibleInstances, PartialTypeSignatures, MultiParamTypeClasses, FlexibleContexts, TypeFamilies, StandaloneKindSignatures, GADTs, RebindableSyntax, PolyKinds, UndecidableInstances, TypeOperators #-}
module Store where

import Prelude hiding (Monad(..), (=<<))
import Data.Kind (Type, Constraint)
import GHC.TypeLits (TypeError, ErrorMessage(..))
import Utils

newtype Task = Task ()
newtype Machine = Machine ()

run :: Task -> Machine -> IProg StateF StateG p p ()
run = undefined

machineInit :: Machine
machineInit = undefined

task1, task2 :: Task
task1 = undefined
task2 = undefined

(=<<) :: (_) => _
(=<<) = flip (>>=)

lazyInit cache = do
    get cache >>= \case
      Just machine  ->  do
        --demandPut cache
        return machine
      Nothing       ->  do
        let machine = machineInit
        put cache (Just machine)
        return machine

runMultipleTasks = do
  cache <- alloc Nothing
  fork (run task1 =<< lazyInit cache)
  --fork (run task2 =<< lazyInit cache)
  return ()

pounds = id

transfer sender recipient amount = do
  v_sender <- get sender
  v_recipient <- get recipient
  put sender (v_sender - amount)
  put recipient (v_recipient + amount)

racyBank = do
  alice <- alloc (pounds 10)
  bob <- alloc (pounds 10)
  fork (transfer alice bob (pounds 5))
  --fork (transfer alice bob (pounds 5))

test = do
  a <- alloc False
  put a True
  get a
  fork $ do
    put a False
    return ()
  return ()