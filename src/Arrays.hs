{-# OPTIONS_GHC -fplugin=Plugin #-}

{-# LANGUAGE BlockArguments, TypeOperators, DataKinds, FlexibleInstances, PartialTypeSignatures, MultiParamTypeClasses, FlexibleContexts, TypeFamilies, TypeApplications, ScopedTypeVariables, StandaloneKindSignatures, GADTs, RebindableSyntax, PolyKinds #-}
module Arrays where

import Data.Kind (Type, Constraint)
import Utils
import Prelude hiding (Monad(..), read, length, fold)
import qualified Prelude as P
import qualified Data.Array.IO as IO
import GHC.Types (Any)
import Unsafe.Coerce (unsafeCoerce)
import Control.Monad.STM (atomically)
import Control.Concurrent.STM.TMVar (TMVar, newEmptyTMVarIO, putTMVar, takeTMVar)
import Control.Concurrent (forkIO)
import System.Random
import Data.Complex

ifThenElse True a _ = a
ifThenElse False _ b = b

dot :: [Int] -> [Int] -> Int
dot [a,b,c] [x,y,z] = a * x + b * y + c * z 

when :: (IMonad m) => Bool -> m i i () -> m i i ()
when False _ = return ()
when True a  = a `seq` a

foldM :: (IMonad m) => [a] -> c -> (a -> c -> m i i c) -> m i i c
foldM [x] c f
  = f x c
foldM (x:xs) c f
  = f x c >>= \c' -> foldM xs c' f

partition :: (_) => Int -> AToken t v n -> IProg Array Thread c c Int
partition len arr = do
  let last = len - 1 -- c
  pivot <- read arr last
  i <- foldM [0..(last - 1)] 0 \j i -> do
    j_value <- read arr j
    if j_value < pivot then do
      i_value <- read arr i
      write arr j i_value
      write arr i j_value
      return (i + 1)
    else
      return i
  i_value <- read arr i
  write arr i pivot
  write arr last i_value -- c
  return i

type Bounds = (Int, Int)
unsafeCreate :: forall a t v n. a -> AToken t v n
unsafeCreate = AToken
unsafeUncover :: forall a t v n. AToken t v n -> a
unsafeUncover (AToken a) = unsafeCoerce a
unsafeCreateA = unsafeCreate @(Bounds, IO.IOArray Int Any)
unsafeUncoverA = unsafeUncover @(Bounds, IO.IOArray Int Any)

runArrays
  :: IProg Array Thread '[] q a
  -> IO ()
runArrays prog = (runArraysH prog) P.>> (P.return ())

runArraysH
  :: IProg Array Thread p q a
  -> IO [TMVar ()]
runArraysH (Pure a) = P.return []
runArraysH (Impure (Malloc i (a :: b)) c) 
  = let upper = i - 1 in
    let bounds = (0, upper) in
    (IO.newArray bounds a :: IO (IO.IOArray Int b)) P.>>=
    (\arr -> let arr' = (unsafeCoerce arr :: IO.IOArray Int Any) in
    runArraysH (c (unsafeCreateA (bounds, arr'))))
runArraysH (Impure (Read n i) c)
  = let ((lower, upper), arr) = unsafeUncoverA n in
    let offset = i + lower in
    if offset > upper || offset < lower
      then error $ "Index out of bounds " ++ show (lower, upper) ++ " " ++ show i
      else
        (IO.readArray (arr :: IO.IOArray Int Any) offset) P.>>=
        (\v -> v `seq` runArraysH (c (unsafeCoerce v)))
runArraysH (Impure (Write n i (a :: b)) c)
  = let ((lower, upper), arr) = unsafeUncoverA n in
    let offset = i + lower in
    if offset > upper || offset < lower
      then error "Index out of bounds"
      else 
        (IO.writeArray (unsafeCoerce arr :: IO.IOArray Int b) offset a) P.>>=
        (\v -> v `seq` runArraysH (c ()))
runArraysH (Impure (Length n) c)
  = let ((lower, upper), arr) = unsafeUncoverA n in
    if upper - lower + 1 < 0
      then error "Should not be here"
      else runArraysH (c (upper - lower + 1))
runArraysH (Impure (Join a b) c)
  = runArraysH (c ())
runArraysH (Impure (Split n i) c)
  = let ((lower, upper), arr) = unsafeUncoverA n in
    let offset = i + lower in
    if offset > upper || offset < lower
      then error ("Index out of bounds " ++ show i ++ " " ++ show (lower, upper))
      else
        let n1 = (lower, offset) in
        let n2 = (offset + 1, upper) in
        runArraysH (c (unsafeCreateA (n1, arr), unsafeCreateA (n2, arr)))
runArraysH (Impure (InjectIO a) c)
  = a P.>>= (runArraysH . c)
runArraysH (Scope AFork c a)
  = newEmptyTMVarIO P.>>=
    (\var -> {-forkIO ( -}
      (runArraysH c) P.>>= (atomically . mapM_ takeTMVar) P.>> (atomically (putTMVar var ()) {-)-}
    ) P.>> (runArraysH (a Future)) P.>>=
    (\result -> P.return (var:result)))
runArraysH (Scope AFinish c a)
  = runArraysH c P.>>= (atomically . mapM_ takeTMVar) P.>> runArraysH (a ())

runArraysH _ = undefined

forM_ :: (IMonad m) => [a] -> (a -> m i i ()) -> m i i ()
forM_ [x] f
  = f x
forM_ (x:xs) f
  = f x >>= \c -> forM_ xs f

example6 :: IO ()
example6 = runArrays $ do
  let length = 10
  injectIO (putStrLn "Hello")
  arr <- malloc length 0
  write arr 0 10
  forM_ [0..(length - 1)] $ \i -> do
    j <- injectIO (getStdRandom (randomR @Int (1,100000)))
    write arr i j
  forM_ [0..(length - 1)] $ \i -> do
    j <- read arr i
    injectIO (putStrLn $ (show i) ++ ": " ++ (show j))
  injectIO (putStrLn "sorting...")
  quicksort arr
  injectIO (putStrLn "end sorting...")
  forM_ [0..(length - 1)] $ \i -> do
    j <- read arr i
    injectIO (putStrLn $ (show i) ++ ": " ++ (show j))

example20 :: IO ()
example20 = runArrays $ do
  let length = 20
  injectIO (putStrLn "Hello")
  arr <- malloc length 0
  write arr 0 10
  forM_ [0..(length - 1)] $ \i -> do
    j <- injectIO (getStdRandom (randomR @Int (1,5)))
    write arr i j
  forM_ [0..(length - 1)] $ \i -> do
    j <- read arr i
    injectIO (putStrLn $ (show i) ++ ": " ++ (show j))
  injectIO (putStrLn "convolving...")
  parallelConvolve 0 0 arr [1,2,3]
  injectIO (putStrLn "end convolving...")
  forM_ [0..(length - 1)] $ \i -> do
    j <- read arr i
    injectIO (putStrLn $ (show i) ++ ": " ++ (show j))

type CDouble = Complex Double
type Info = (Int, Int, Int) -- Start, Gap, Len

toDouble :: (Integral a) => a -> Double
toDouble = fromIntegral

example21 :: IO ()
example21 = runArrays $ do
  let length = 8
  injectIO (putStrLn "Hello")
  arr <- malloc length 0
  output <- malloc length 0
  write arr 0 10
  forM_ [0..(length - 1)] $ \i -> do
    j <- injectIO (getStdRandom (randomR @Int (1,5)))
    write arr i (toDouble j :+ 0)
  forM_ [0..(length - 1)] $ \i -> do
    j <- read arr i
    injectIO (putStrLn $ (show i) ++ ": " ++ (show j))
  injectIO (putStrLn "ffting...")
  fft arr output (0, 1, 8)
  injectIO (putStrLn "end ffting...")
  forM_ [0..(length - 1)] $ \i -> do
    j <- read output i
    injectIO (putStrLn $ (show i) ++ ": " ++ (show j))

quicksort  ::  (X ≤ Lookup p n)
           =>  AToken Int r n
           ->  IProg Array Thread p p ()
quicksort arr = do
  len <- length arr
  if len <= 2 then do
    when (len == 2) do
        v0 <- read arr 0
        v1 <- read arr 1
        when (v0 > v1) do
          write arr 0 v1
          write arr 1 v0
  else afinish do
    i <- partition len arr
    (i1, i2) <- slice arr (max (i - 1) 0)
    afork do 
      quicksort i1
    quicksort i2
    return ()

serialConvolve before after inputs weights = do
      len <- length inputs
      foldM [0..(len - 1)] before $ \i prevEl -> do
        let j = i + 1
        currEl <- read inputs i
        nextEl <- if j == len 
          then return after
          else read inputs j
        let sum = [prevEl, currEl, nextEl] `dot` weights 
        write inputs i sum
        return currEl
      return ()

parallelConvolve  ::  (X ≤ Lookup p n)
                  =>  Int -> Int -> AToken Int r n -> [Int]
                  ->  IProg Array Thread p p ()
parallelConvolve before after inputs weights = do
  len <- length inputs
  if len < 10 then do
    serialConvolve before after inputs weights
  else afinish do
    let middle = len `div` 2
    middle1 <- read inputs middle
    middle2 <- read inputs (middle + 1)
    (i1, i2) <- slice inputs middle
    afork do 
      parallelConvolve before middle2 i1 weights
    parallelConvolve middle1 after i2 weights
    return ()

realToComplex :: (Integral a) => a -> Complex Double
realToComplex a = (toDouble a) :+ 0

imagToComplex :: Double -> Complex Double
imagToComplex a = 0 :+ a

fft  ::  (R ≤ Lookup p n1, X ≤ Lookup p n2, n1 ≁ n2)
     =>  AToken (Complex Double) r1 n1
     ->  AToken (Complex Double) r2 n2
     ->  (Int, Int, Int)
     ->  IProg Array Thread p p ()
fft input output (start, gap, len) = do
  if len == 1 then do
    v <- read input start
    write output 0 v
  else do
    let offset = len `div` 2
    afinish do
      (output1, output2) <- slice output (offset - 1)
      afork do 
        fft input output1 (start, gap * 2, offset)
      fft input output2 (start + gap, gap * 2, offset)
    forM_ [0..(offset - 1)] $ \j1 -> do
      let j2 = j1 + offset
      x1 <- read output j1
      x2 <- read output j2
      let factor1 = exp $ (-(imagToComplex 2) * pi * (realToComplex j1)) / (realToComplex len)
      let factor2 = exp $ (-(imagToComplex 2) * pi * (realToComplex j2)) / (realToComplex len)
      write output j1 (x1 + factor1 * x2)
      write output j2 (x1 + factor2 * x2)
    return ()
