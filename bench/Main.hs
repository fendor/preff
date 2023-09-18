import FreeExperiment

import Control.Monad.Free
import Control.Monad.Free.Church
import qualified Control.Monad.Free.Church as Church
import Criterion.Main
import Data.Functor.Identity (Identity)

main = do
  let vals :: [Integer]
      vals = [500, 1_000, 5_000, 50_000]
      mkBench n f = bench (show n) $ nf f n
      mkBenches label f = bgroup label $ map (`mkBench` f) vals
  defaultMain
    [ mkBenches "free" freeExp
    , mkBenches "codensity" codensityExp
    , mkBenches "reference" referenceExp
    , mkBenches "church" churchExp
    , mkBenches "churchImproved" churchDirectExp
    , mkBenches "churchImproved'" churchDirectExp'
    , mkBenches "freeMonadExp" freeMonadExp
    , mkBenches "freeMonadExp'" freeMonadExp'
    ]

-- ----------------------------------------------------------------------------
-- Experiment setup
-- ----------------------------------------------------------------------------

freeExp :: Integer -> (Integer, Integer)
freeExp start = runState 0 (prog start >>= prog >>= prog)
 where
  prog s =
    increment s >>= increment >>= increment

codensityExp :: Integer -> (Integer, Integer)
codensityExp start = runStateC 0 (prog start >>= prog >>= prog)
 where
  prog s =
    incrementC s >>= incrementC >>= incrementC

referenceExp :: Integer -> (Integer, Integer)
referenceExp start = case prog start 0 of
  (_, s) -> case prog s s of
    (_, s') -> prog s' s'
 where
  prog i e = case incrementFast i e of
    (_, s) -> case incrementFast s s of
      (_, s') -> incrementFast s' s'

churchExp :: Integer -> (Integer, Integer)
churchExp start = runState 0 (Church.improve $ fromF (prog start >>= prog >>= prog))
 where
  prog s =
    incrementF s >>= incrementF >>= incrementF

freeMonadExp' :: Integer -> (Integer, Integer)
freeMonadExp' start = runState 0 (Church.improve (prog start >>= prog >>= prog))
 where
  prog s =
    incrementM s >>= incrementM >>= incrementM

churchDirectExp :: Integer -> (Integer, Integer)
churchDirectExp start = runStateChurch 0 (prog start >>= prog >>= prog)
 where
  prog s =
    incrementF s >>= incrementF >>= incrementF

churchDirectExp' :: Integer -> (Integer, Integer)
churchDirectExp' start = runStateChurch' 0 (prog start >>= prog >>= prog)
 where
  prog s =
    incrementF' s >>= incrementF' >>= incrementF'

-- ----------------------------------------------------------------------------
-- Local runners for local module optimisation tests
-- ----------------------------------------------------------------------------

runStateChurch' :: e -> F (StateF e) a -> (a, e)
runStateChurch' start op =
  ( runF
      op
      (\a s -> (a, s))
      ( \cases
          (Get k) s -> k s s
          (Put e k) s' -> k e
      )
  )
    start

-- ----------------------------------------------------------------------------
-- Local increment code for local module optimisation tests
-- ----------------------------------------------------------------------------

incrementF' :: Integer -> F (StateF Integer) Integer
incrementF' n = do
  if n <= 0
    then getF
    else do
      x <- getF
      putF (x + 1)
      incrementF' (n - 1)
