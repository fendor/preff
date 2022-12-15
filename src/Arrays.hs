{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE RebindableSyntax #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# OPTIONS_GHC -fplugin=Plugin #-}

{-# HLINT ignore "Use foldM_" #-}
{-# HLINT ignore "Use void" #-}

module Arrays where

import Data.Complex
import Parameterised.Array
import System.Random
import MiniEff
import Prelude hiding (Monad (..), length, read)

dot :: [Int] -> [Int] -> Int
dot [a, b, c] [x, y, z] = a * x + b * y + c * z
dot _ _ = error "dot"

partition :: (Ord t, 'R ≤ Lookup c n, 'X ≤ Lookup c n) => Int -> AToken t v n -> MiniEff effs Array Thread c c Int
partition len arr = do
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

example6 :: IO ()
example6 = runArrays $ do
  let len = 10
  injectIO (putStrLn "Hello")
  arr <- malloc len 0
  write arr 0 10
  forM_ [0 .. (len - 1)] $ \i -> do
    j <- injectIO (getStdRandom (randomR @Int (1, 100000)))
    write arr i j
  forM_ [0 .. (len - 1)] $ \i -> do
    j <- read arr i
    injectIO (putStrLn $ show i ++ ": " ++ show j)
  injectIO (putStrLn "sorting...")
  quicksort arr
  injectIO (putStrLn "end sorting...")
  forM_ [0 .. (len - 1)] $ \i -> do
    j <- read arr i
    injectIO (putStrLn $ show i ++ ": " ++ show j)

example20 :: IO ()
example20 = runArrays $ do
  let len = 20
  injectIO (putStrLn "Hello")
  arr <- malloc len 0
  write arr 0 10
  forM_ [0 .. (len - 1)] $ \i -> do
    j <- injectIO (getStdRandom (randomR @Int (1, 5)))
    write arr i j
  forM_ [0 .. (len - 1)] $ \i -> do
    j <- read arr i
    injectIO (putStrLn $ show i ++ ": " ++ show j)
  injectIO (putStrLn "convolving...")
  parallelConvolve 0 0 arr [1, 2, 3]
  injectIO (putStrLn "end convolving...")
  forM_ [0 .. (len - 1)] $ \i -> do
    j <- read arr i
    injectIO (putStrLn $ show i ++ ": " ++ show j)

type CDouble = Complex Double
type Info = (Int, Int, Int) -- Start, Gap, Len

toDouble :: (Integral a) => a -> Double
toDouble = fromIntegral

example21 :: IO ()
example21 = runArrays $ do
  let len = 8
  injectIO (putStrLn "Hello")
  arr <- malloc len 0
  output <- malloc len 0
  write arr 0 10
  forM_ [0 .. (len - 1)] $ \i -> do
    j <- injectIO (getStdRandom (randomR @Int (1, 5)))
    write arr i (toDouble j :+ 0)
  forM_ [0 .. (len - 1)] $ \i -> do
    j <- read arr i
    injectIO (putStrLn $ show i ++ ": " ++ show j)
  injectIO (putStrLn "ffting...")
  fft arr output (0, 1, 8)
  injectIO (putStrLn "end ffting...")
  forM_ [0 .. (len - 1)] $ \i -> do
    j <- read output i
    injectIO (putStrLn $ show i ++ ": " ++ show j)

quicksort ::
  (X ≤ Lookup p n) =>
  AToken Int r n ->
  MiniEff effs Array Thread p p ()
quicksort arr = do
  len <- length arr
  if len <= 2
    then do
      when (len == 2) do
        v0 <- read arr 0
        v1 <- read arr 1
        when (v0 > v1) do
          write arr 0 v1
          write arr 1 v0
    else afinish do
      i <- partition len arr
      (i1, i2) <- slice arr (max (i - 1) 0)
      _ <- afork do
        quicksort i1
      quicksort i2
      return ()

serialConvolve ::
  forall
    k1
    (k2 :: [AccessLevel])
    (n :: Nat)
    (v :: k1)
    (g :: [AccessLevel] -> [AccessLevel] -> [AccessLevel] -> [AccessLevel] -> * -> * -> *)
    effs.
  ( 'R ≤ Lookup k2 n, 'X ≤ Lookup k2 n) =>
  Int ->
  Int ->
  AToken Int v n ->
  [Int] ->
  MiniEff effs Array g k2 k2 ()
serialConvolve before after inputs weights = do
  len <- length inputs
  _ <- foldM [0 .. (len - 1)] before $ \i prevEl -> do
    let j = i + 1
    currEl <- read inputs i
    nextEl <-
      if j == len
        then return after
        else read inputs j
    let sumRes = [prevEl, currEl, nextEl] `dot` weights
    write inputs i sumRes
    return currEl
  return ()

parallelConvolve ::
  (X ≤ Lookup p n) =>
  Int ->
  Int ->
  AToken Int r n ->
  [Int] ->
  MiniEff effs Array Thread p p ()
parallelConvolve before after inputs weights = do
  len <- length inputs
  if len < 10
    then do
      serialConvolve before after inputs weights
    else afinish do
      let middle = len `div` 2
      middle1 <- read inputs middle
      middle2 <- read inputs (middle + 1)
      (i1, i2) <- slice inputs middle
      _ <- afork do
        parallelConvolve before middle2 i1 weights
      parallelConvolve middle1 after i2 weights
      return ()

realToComplex :: (Integral a) => a -> Complex Double
realToComplex a = toDouble a :+ 0

imagToComplex :: Double -> Complex Double
imagToComplex a = 0 :+ a

fft ::
  (R ≤ Lookup p n1, X ≤ Lookup p n2, n1 ≁ n2) =>
  AToken (Complex Double) r1 n1 ->
  AToken (Complex Double) r2 n2 ->
  (Int, Int, Int) ->
  MiniEff effs Array Thread p p ()
fft input output (start, gap, len) = do
  if len == 1
    then do
      v <- read input start
      write output 0 v
    else do
      let offset = len `div` 2
      afinish do
        (output1, output2) <- slice output (offset - 1)
        _ <- afork do
          fft input output1 (start, gap * 2, offset)
        fft input output2 (start + gap, gap * 2, offset)
      forM_ [0 .. (offset - 1)] $ \j1 -> do
        let j2 = j1 + offset
        x1 <- read output j1
        x2 <- read output j2
        let factor1 = exp $ (-imagToComplex 2 * pi * realToComplex j1) / realToComplex len
        let factor2 = exp $ (-imagToComplex 2 * pi * realToComplex j2) / realToComplex len
        write output j1 (x1 + factor1 * x2)
        write output j2 (x1 + factor2 * x2)
