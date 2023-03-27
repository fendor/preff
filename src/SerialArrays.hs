{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE QualifiedDo #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}

-- {-# OPTIONS_GHC -fplugin=Plugin #-}

{-# HLINT ignore "Use foldM_" #-}
{-# HLINT ignore "Use void" #-}

module SerialArrays where

import qualified Data.Array.IO as IO
import Data.Complex
import GHC.Types (Any)
import PrEff.Parameterised.Array hiding (afork, join, length, malloc, read, slice, write)
import Unsafe.Coerce (unsafeCoerce)
import PrEff
import qualified Control.IxMonad as Ix
import Prelude hiding (Monad (..), length, read)

afork a = ScopedP (AFork a) emptyCont

join i1 i2 = ImpureP (Join i1 i2) $ IKleisliTupled Ix.return

write a b c = ImpureP (Write a b c) $ IKleisliTupled Ix.return

malloc a b = ImpureP (Malloc a b) $ IKleisliTupled Ix.return

slice a b = ImpureP (Split a b) $ IKleisliTupled Ix.return

length a = ImpureP (Length a) $ IKleisliTupled Ix.return

read a b = ImpureP (Read a b) $ IKleisliTupled Ix.return

runSerialArrays ::
  (Member IIO effs) =>
  PrEff effs Array p q a ->
  PrEff effs IVoid () () a
runSerialArrays (Value a) = Ix.return a
runSerialArrays (ScopedP _ _) = error "Test"
runSerialArrays (Impure cmd k) =
  -- unsafeCoerce is currently necessary because GHC fails to unify:
  --
  -- expected: PrEff (IIO : effs) IVoid sr2       (u : qs) a
  -- actual:   PrEff (IIO : effs) IVoid (u : ps0) (u : qs) a
  --
  -- Maybe we can pass somehow that sr2 ~ (u: ps0)
  Impure cmd (IKleisliTupled $ \x -> runSerialArrays $ runIKleisliTupled k x)
runSerialArrays (ImpureP cmd k) = case cmd of
  Malloc i (a :: b) -> Ix.do
    let bounds = (0, i - 1)
    arr <- embedIO (IO.newArray bounds a :: IO (IO.IOArray Int b))
    let arr' = unsafeCoerce arr :: IO.IOArray Int Any
    runSerialArrays (runIKleisliTupled k (unsafeCreateA (bounds, arr')))
  Read n i -> Ix.do
    let ((lower, upper), arr) = unsafeUncoverA n
        offset = i + lower
    if offset > upper || offset < lower
      then error $ "Index out of bounds " ++ show (lower, upper)
      else Ix.do
        v <- embedIO $ (IO.readArray (arr :: IO.IOArray Int Any) offset :: IO Any)
        v `seq` runSerialArrays (runIKleisliTupled k $ unsafeCoerce v)
  Write n i (a :: b) -> Ix.do
    let ((lower, upper), arr) = unsafeUncoverA n
        offset = i + lower
    if offset > upper || offset < lower
      then error $ "Index out of bounds " ++ show (lower, upper)
      else Ix.do
        v <- embedIO $ (IO.writeArray (unsafeCoerce arr :: IO.IOArray Int b) offset a :: IO ())
        v `seq` runSerialArrays (runIKleisliTupled k ())
  Length n -> Ix.do
    let ((lower, upper), _) = unsafeUncoverA n
    if upper - lower + 1 < 0
      then error "Should not be here"
      else runSerialArrays $ runIKleisliTupled k (upper - lower + 1)
  Join _a _b -> Ix.do
    runSerialArrays $ runIKleisliTupled k ()
  Split n i -> Ix.do
    let ((lower, upper), arr) = unsafeUncoverA n
        offset = i + lower
    if offset > upper || offset < lower
      then error $ "Index out of bounds " ++ show (lower, upper)
      else Ix.do
        let n1 = (lower, offset)
            n2 = (offset + 1, upper)
        runSerialArrays $ runIKleisliTupled k (unsafeCreateA (n1, arr), unsafeCreateA (n2, arr))
  Wait _ -> error "Wait has no point, atm"
  InjectIO _ -> error "Don't use injectIO!"

serialConvolve ::
  forall k1 (k2 :: [AccessLevel]) (n :: Nat) (v :: k1) eff.
  ( 'R ≤ Lookup k2 n, 'X ≤ Lookup k2 n) =>
  Int ->
  Int ->
  AToken Int v n ->
  [Int] ->
  PrEff eff Array k2 k2 ()
serialConvolve before after inputs weights = Ix.do
  len <- length inputs
  _ <- foldM [0 .. (len - 1)] before $ \i prevEl -> Ix.do
    let j = i + 1
    currEl <- read inputs i
    nextEl <-
      if j == len
        then Ix.return after
        else read inputs j
    let sumRes = [prevEl, currEl, nextEl] `dot` weights
    write inputs i sumRes
    Ix.return currEl
  Ix.return ()

realToComplex :: (Integral a) => a -> Complex Double
realToComplex a = toDouble a :+ 0

imagToComplex :: Double -> Complex Double
imagToComplex a = 0 :+ a

toDouble :: (Integral a) => a -> Double
toDouble = fromIntegral

forM_ :: (Ix.IMonad m) => [a] -> (a -> m i i ()) -> m i i ()
forM_ [] _ = Ix.return ()
forM_ [x] f =
  f x
forM_ (x : xs) f =
  f x Ix.>>= \_c -> forM_ xs f

dot :: [Int] -> [Int] -> Int
dot [a, b, c] [x, y, z] = a * x + b * y + c * z
dot _ _ = error "dot"
