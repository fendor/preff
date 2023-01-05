{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE RebindableSyntax #-}
{-# LANGUAGE UndecidableInstances #-}

module Store where

import MiniEff.Parameterised.State
import MiniEff
import Prelude hiding (Monad (..), (=<<))
import Control.IxMonad as Ix

newtype Task = Task ()
newtype Machine = Machine ()

run :: Task -> Machine -> MiniEff effs StateF p p ()
run = undefined

machineInit :: Machine
machineInit = undefined

task1, task2 :: Task
task1 = undefined
task2 = undefined

(=<<) :: (IMonad m) => ((a -> m j k b) -> m i j a -> m i k b)
(=<<) = flip (>>=)

lazyInit :: ( 'R ≤ Lookup j n, 'X ≤ Lookup j n) => Token (Maybe Machine) n -> MiniEff effs StateF j j Machine
lazyInit cache = Ix.do
  get cache >>= \case
    Just machine -> do
      --demandPut cache
      return machine
    Nothing -> do
      let machine = machineInit
      put cache (Just machine)
      return machine

runMultipleTasks :: MiniEff effs StateF i k ()
runMultipleTasks = do
  cache <- alloc Nothing
  _ <- fork (Store.run task1 =<< lazyInit cache)
  -- fork (run task2 =<< lazyInit cache)
  return ()

pounds :: Int -> Int
pounds = id

transfer ::
  ( Num a
  , 'R ≤ Lookup k n1
  , 'R ≤ Lookup k n2
  , 'X ≤ Lookup k n1
  , 'X ≤ Lookup k n2
  ) =>
  Token a n1 ->
  Token a n2 ->
  a ->
  MiniEff effs StateF k k ()
transfer sender recipient amount = do
  v_sender <- get sender
  v_recipient <- get recipient
  put sender (v_sender - amount)
  put recipient (v_recipient + amount)

racyBank :: MiniEff effs StateF i k (Future ())
racyBank = do
  alice <- alloc (pounds 10)
  bob <- alloc (pounds 10)
  fork (transfer alice bob (pounds 5))

--fork (transfer alice bob (pounds 5))

test :: MiniEff effs StateF i k ()
test = do
  a <- alloc False
  put a True
  _ <- get a
  _ <- fork $ do
    put a False
    return ()
  return ()
