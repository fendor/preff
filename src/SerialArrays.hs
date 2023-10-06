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

join i1 i2 = sendP (Join i1 i2)

write a b c = sendP (Write a b c)

malloc a b = sendP (Malloc a b)

slice a b = sendP (Split a b)

length a = sendP (Length a)

read a b = sendP (Read a b)

runSerialArrays ::
  (Member (Embed IO) effs) =>
  PrEff effs Array p q a ->
  PrEff effs IVoid () () a
runSerialArrays (Value a) = pure a
runSerialArrays (ScopedP _ _) = error "Test"
runSerialArrays (Impure cmd k) =
  Impure cmd (iKleisli $ \x -> runSerialArrays $ runIKleisli k x)
runSerialArrays (ImpureP cmd k) = case cmd of
  Malloc i (a :: b) -> Ix.do
    let bounds = (0, i - 1)
    arr <- embedIO (IO.newArray bounds a :: IO (IO.IOArray Int b))
    let arr' = unsafeCoerce arr :: IO.IOArray Int Any
    runSerialArrays (runIKleisli k (unsafeCreateA (bounds, arr')))
  Read n i -> Ix.do
    let ((lower, upper), arr) = unsafeUncoverA n
        offset = i + lower
    if offset > upper || offset < lower
      then error $ "Index out of bounds " ++ show (lower, upper)
      else Ix.do
        v <- embedIO $ (IO.readArray (arr :: IO.IOArray Int Any) offset :: IO Any)
        v `seq` runSerialArrays (runIKleisli k $ unsafeCoerce v)
  Write n i (a :: b) -> Ix.do
    let ((lower, upper), arr) = unsafeUncoverA n
        offset = i + lower
    if offset > upper || offset < lower
      then error $ "Index out of bounds " ++ show (lower, upper)
      else Ix.do
        v <- embedIO $ (IO.writeArray (unsafeCoerce arr :: IO.IOArray Int b) offset a :: IO ())
        v `seq` runSerialArrays (runIKleisli k ())
  Length n -> Ix.do
    let ((lower, upper), _) = unsafeUncoverA n
    if upper - lower + 1 < 0
      then error "Should not be here"
      else runSerialArrays $ runIKleisli k (upper - lower + 1)
  Join _a _b -> Ix.do
    runSerialArrays $ runIKleisli k ()
  Split n i -> Ix.do
    let ((lower, upper), arr) = unsafeUncoverA n
        offset = i + lower
    if offset > upper || offset < lower
      then error $ "Index out of bounds " ++ show (lower, upper)
      else Ix.do
        let n1 = (lower, offset)
            n2 = (offset + 1, upper)
        runSerialArrays $ runIKleisli k (unsafeCreateA (n1, arr), unsafeCreateA (n2, arr))
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
  _ <- Ix.foldM [0 .. (len - 1)] before $ \i prevEl -> Ix.do
    let j = i + 1
    currEl <- read inputs i
    nextEl <-
      if j == len
        then pure after
        else read inputs j
    let sumRes = [prevEl, currEl, nextEl] `dot` weights
    write inputs i sumRes
    pure currEl
  pure ()

realToComplex :: (Integral a) => a -> Complex Double
realToComplex a = toDouble a :+ 0

imagToComplex :: Double -> Complex Double
imagToComplex a = 0 :+ a

toDouble :: (Integral a) => a -> Double
toDouble = fromIntegral

dot :: [Int] -> [Int] -> Int
dot [a, b, c] [x, y, z] = a * x + b * y + c * z
dot _ _ = error "dot"
