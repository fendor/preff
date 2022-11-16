{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE RebindableSyntax #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}

-- {-# OPTIONS_GHC -fplugin=Plugin #-}

{-# HLINT ignore "Use foldM_" #-}
{-# HLINT ignore "Use void" #-}

module SerialArrays where

import qualified Data.Array.IO as IO
import GHC.Types (Any)
import Parameterised.Array hiding (join, length, malloc, read, slice, write)
import Unsafe.Coerce (unsafeCoerce)
import Utils
import Prelude hiding (Monad (..), length, read)

join i1 i2 = Impure (OHere $ Join i1 i2) $ IKleisliTupled return

write a b c = Impure (OHere $ Write a b c) $ IKleisliTupled return

malloc a b = Impure (OHere $ Malloc a b) $ IKleisliTupled return

slice a b = Impure (OHere $ Split a b) $ IKleisliTupled return

length a = Impure (OHere $ Length a) $ IKleisliTupled return

read a b = Impure (OHere $ Read a b) $ IKleisliTupled return

runSerialArrays :: IProg (Op (Array: effs)) IVoid (p : ps) (q : qs) a -> IProg (Op (IIO : effs)) IVoid (u: ps) (u: qs) a
runSerialArrays (Pure a) = return a
runSerialArrays (Scope _ _) = error "Test"
-- _ :: IProg (Op (Array: IIO: effs)) IVoid (p: sr2) (q: u: t) a
--   -> IProg (Op (IIO : effs)) IVoid sr2 (u : t) a
-- _ :: IProg (Op (Array: IIO: effs)) IVoid (p: u: s) (q: u: t) a
--   -> IProg (Op (IIO: effs)) IVoid (u: s) (u: t) a
runSerialArrays (Impure (OThere cmd) k) = error "runSerialArrays: singleton effect array"
runSerialArrays (Impure (OHere cmd) k) = case cmd of
  Malloc i (a :: b) -> do
    let bounds = (0, i - 1)
    arr <- embedIO1 (IO.newArray bounds a :: IO (IO.IOArray Int b))
    let arr' = unsafeCoerce arr :: IO.IOArray Int Any
    runSerialArrays (runIKleisliTupled k (unsafeCreateA (bounds, arr')))
  Read n i -> do
    let ((lower, upper), arr) = unsafeUncoverA n
        offset = i + lower
    if offset > upper || offset < lower
      then error $ "Index out of bounds " ++ show (lower, upper)
      else do
        v <- embedIO1 $ (IO.readArray (arr :: IO.IOArray Int Any) offset :: IO Any)
        v `seq` runSerialArrays (runIKleisliTupled k $ unsafeCoerce v)
  Write n i (a :: b) -> do
    let ((lower, upper), arr) = unsafeUncoverA n
        offset = i + lower
    if offset > upper || offset < lower
      then error $ "Index out of bounds " ++ show (lower, upper)
      else do
        v <- embedIO1 $ (IO.writeArray (unsafeCoerce arr :: IO.IOArray Int b) offset a :: IO ())
        v `seq` runSerialArrays (runIKleisliTupled k ())
  Length n -> do
    let ((lower, upper), _) = unsafeUncoverA n
    if upper - lower + 1 < 0
      then error "Should not be here"
      else runSerialArrays $ runIKleisliTupled k (upper - lower + 1)
  Join _a _b -> do
    runSerialArrays $ runIKleisliTupled k ()
  Split n i -> do
    let ((lower, upper), arr) = unsafeUncoverA n
        offset = i + lower
    if offset > upper || offset < lower
      then error $ "Index out of bounds " ++ show (lower, upper)
      else do
        let n1 = (lower, offset)
            n2 = (offset + 1, upper)
        runSerialArrays $ runIKleisliTupled k (unsafeCreateA (n1, arr), unsafeCreateA (n2, arr))
  Wait _ -> error "Wait has no point, atm"
  InjectIO _ -> error "Don't use injectIO!"

embedIO1 :: IO a -> IProg (Op (IIO: effs)) IVoid (u: ps) (u: qs) a
embedIO1 io = Impure (OHere $ RunIO io) emptyCont
