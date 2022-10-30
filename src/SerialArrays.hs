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
import qualified Fcf

join i1 i2 = Op (Inl $ Join i1 i2) $ IKleisliTupled return

write a b c = Op (Inl $ Write a b c) $ IKleisliTupled return

malloc a b = Op (Inl $ Malloc a b) $ IKleisliTupled return

slice a b = Op (Inl $ Split a b) $ IKleisliTupled return

length a = Op (Inl $ Length a) $ IKleisliTupled return

read a b = Op (Inl $ Read a b) $ IKleisliTupled return

runSerialArrays :: Sem (Array :+: IIO) '(p, u) '(q, v) a -> Sem IIO u v a
runSerialArrays (Value a) = return a
runSerialArrays (Op (Inr cmd) k) = Op cmd $ IKleisliTupled $ \x -> runSerialArrays $ runIKleisliTupled k x
runSerialArrays (Op (Inl cmd) k) = case cmd of
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
        v <- embedIO1 $ IO.readArray (arr :: IO.IOArray Int Any) offset
        v `seq` runSerialArrays (runIKleisliTupled k $ unsafeCoerce v)
  Write n i (a :: b) -> do
    let ((lower, upper), arr) = unsafeUncoverA n
        offset = i + lower
    if offset > upper || offset < lower
      then error $ "Index out of bounds " ++ show (lower, upper)
      else do
        v <- embedIO1 $ IO.writeArray (unsafeCoerce arr :: IO.IOArray Int b) offset a
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

quicksortS ::
  (X ≤ Fcf.Eval (Lookup p n), R ≤ Fcf.Eval (Lookup p n)) =>
  AToken Int r n ->
  Sem (Array :+: IIO) '(p, ()) '(p, ()) ()
quicksortS arr = do
  len <- length arr
  if len <= 2
    then do
      when (len == 2) do
        v0 <- read arr 0
        v1 <- read arr 1
        when (v0 > v1) do
          write arr 0 v1
          write arr 1 v0
    else do
      i <- partitionS len arr
      (i1, i2) <- slice arr (max (i - 1) 0)
      -- quicksortS i1
      -- quicksortS i2
      join i1 i2

-- >>> :kind! Replace '[X] 'Z 'N
partitionS :: (Ord t, 'R ≤ Fcf.Eval (Lookup c n), 'X ≤ Fcf.Eval (Lookup c n)) => Int -> AToken t v n -> Sem (Array :+: IIO) '(c, p) '(c, p) Int
partitionS len arr = do
  let lastIndex = len - 1 -- c
  pivot <- read arr lastIndex
  i <- foldM [0 .. (lastIndex - 1)] 0 \j i -> do
    j_value <- read arr j
    if j_value < pivot
      then do
        i_value <- read arr i
        write arr j i_value
        write arr i j_value
        return (i + 1)
      else return i
  i_value <- read arr i
  write arr i pivot
  write arr lastIndex i_value -- c
  return i
