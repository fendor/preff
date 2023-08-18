{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE QualifiedDo #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}

-- {-# OPTIONS_GHC -fplugin=Plugin #-}

{-# HLINT ignore "Use foldM_" #-}
{-# HLINT ignore "Use void" #-}

module SerialArrays where

import Data.Complex
import qualified Data.Array.IO as IO
import GHC.Types (Any)
import Parameterised.Array hiding (join, length, malloc, read, slice, write, afork)
import Unsafe.Coerce (unsafeCoerce)
import Utils
import qualified Utils as I
import Prelude hiding (Monad (..), length, read)

afork a = Scope (AFork a) pure

join i1 i2 = Impure (OHere $ Join i1 i2) $ IKleisliTupled return

write a b c = Impure (OHere $ Write a b c) $ IKleisliTupled return

malloc a b = Impure (OHere $ Malloc a b) $ IKleisliTupled return

slice a b = Impure (OHere $ Split a b) $ IKleisliTupled return

length a = Impure (OHere $ Length a) $ IKleisliTupled return

read a b = Impure (OHere $ Read a b) $ IKleisliTupled return


runSerialArrays :: forall effs p q u ps a qs. IProg (Array: IIO: effs) IVoid (p : u: ps) (q : u: qs) a -> IProg (IIO : effs) IVoid (u: ps) (u: qs) a
runSerialArrays (Pure a) = return a
runSerialArrays (Scope _ _) = error "Test"
runSerialArrays (Impure (OThere cmd) k) =
  -- unsafeCoerce is currently necessary because GHC fails to unify:
  --
  -- expected: IProg (IIO : effs) IVoid sr2       (u : qs) a
  -- actual:   IProg (IIO : effs) IVoid (u : ps0) (u : qs) a
  --
  -- Maybe we can pass somehow that sr2 ~ (u: ps0)
  Impure cmd (IKleisliTupled $ \x -> unsafeCoerce runSerialArrays $ runIKleisliTupled k x)
runSerialArrays (Impure (OHere cmd) k) = case cmd of
  Malloc i (a :: b) -> I.do
    let bounds = (0, i - 1)
    arr <- embedIO1 (IO.newArray bounds a :: IO (IO.IOArray Int b))
    let arr' = unsafeCoerce arr :: IO.IOArray Int Any
    runSerialArrays (runIKleisliTupled k (unsafeCreateA (bounds, arr')))
  Read n i -> I.do
    let ((lower, upper), arr) = unsafeUncoverA n
        offset = i + lower
    if offset > upper || offset < lower
      then error $ "Index out of bounds " ++ show (lower, upper)
      else I.do
        v <- embedIO1 $ (IO.readArray (arr :: IO.IOArray Int Any) offset :: IO Any)
        v `seq` runSerialArrays (runIKleisliTupled k $ unsafeCoerce v)
  Write n i (a :: b) -> I.do
    let ((lower, upper), arr) = unsafeUncoverA n
        offset = i + lower
    if offset > upper || offset < lower
      then error $ "Index out of bounds " ++ show (lower, upper)
      else I.do
        v <- embedIO1 $ (IO.writeArray (unsafeCoerce arr :: IO.IOArray Int b) offset a :: IO ())
        v `seq` runSerialArrays (runIKleisliTupled k ())
  Length n -> I.do
    let ((lower, upper), _) = unsafeUncoverA n
    if upper - lower + 1 < 0
      then error "Should not be here"
      else runSerialArrays $ runIKleisliTupled k (upper - lower + 1)
  Join _a _b -> I.do
    runSerialArrays $ runIKleisliTupled k ()
  Split n i -> I.do
    let ((lower, upper), arr) = unsafeUncoverA n
        offset = i + lower
    if offset > upper || offset < lower
      then error $ "Index out of bounds " ++ show (lower, upper)
      else I.do
        let n1 = (lower, offset)
            n2 = (offset + 1, upper)
        runSerialArrays $ runIKleisliTupled k (unsafeCreateA (n1, arr), unsafeCreateA (n2, arr))
  Wait _ -> error "Wait has no point, atm"
  InjectIO _ -> error "Don't use injectIO!"

embedIO1 :: IO a -> IProg (IIO: effs) IVoid (u: ps) (u: ps) a
embedIO1 io = Impure (OHere $ RunIO io) pure

serialConvolve ::
  forall k1 (k2 :: [AccessLevel]) (n :: Nat) (v :: k1) eff sr1.
  ('R ≤ Lookup k2 n, 'X ≤ Lookup k2 n) =>
  Int -> Int -> AToken Int v n -> [Int] -> IProg (Array:eff) IVoid (k2:sr1) (k2:sr1) ()
serialConvolve before after inputs weights = I.do
  len <- length inputs
  _ <- foldM [0 .. (len - 1)] before $ \i prevEl -> I.do
    let j = i + 1
    currEl <- read inputs i
    nextEl <-
      if j == len
        then return after
        else read inputs j
    let sumRes = [prevEl, currEl, nextEl] `dot` weights
    write inputs i sumRes
    return currEl
  I.return ()

realToComplex :: (Integral a) => a -> Complex Double
realToComplex a = toDouble a :+ 0

imagToComplex :: Double -> Complex Double
imagToComplex a = 0 :+ a

toDouble :: (Integral a) => a -> Double
toDouble = fromIntegral

forM_ :: (IMonad m) => [a] -> (a -> m i i ()) -> m i i ()
forM_ [] _ = return ()
forM_ [x] f =
  f x
forM_ (x : xs) f =
  f x >>= \_c -> forM_ xs f

dot :: [Int] -> [Int] -> Int
dot [a, b, c] [x, y, z] = a * x + b * y + c * z
dot _ _ = error "dot"
