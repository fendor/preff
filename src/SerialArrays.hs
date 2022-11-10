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

runSerialArrays :: IProg (Op [Array, IIO]) IVoid '(p, u) '(q, v) a -> IProg (Op '[IIO]) IVoid u v a
runSerialArrays (Pure a) = return a
runSerialArrays (Scope _ _) = error "Test"
-- _ :: IProg (Op (Array: IIO: effs)) IVoid (p: sr2) (q: u: t) a
--   -> IProg (Op (IIO : effs)) IVoid sr2 (u : t) a
-- _ :: IProg (Op (Array: IIO: effs)) IVoid (p: u: s) (q: u: t) a
--   -> IProg (Op (IIO: effs)) IVoid (u: s) (u: t) a
runSerialArrays (Impure (OThere cmd) k) = Impure cmd $ IKleisliTupled (runSerialArrays . cont)
  where
    -- cont :: x -> IProg (Op (Array : IIO : effs)) IVoid (p : sr) (q : v : t) a
    cont x = runIKleisliTupled k x
    -- could not deduce: (sr4 ~ (u1 : s0))
    -- (Array : IIO : effs) ~ (eff : effs1)
    -- (p:u:s) ~ (sl: sr1)
    -- q1 ~ (sl : sr2)
    -- bound by:
    -- OThere :: forall {k} x (eff :: k -> k -> * -> *)
    --           (effs1 :: [k -> k -> * -> *])
    --           (sr1   :: [k])
    --           (sr2   :: [k])
    --           (sl    :: k).
    --   Op effs1 sr1 sr2 x ->
    --   Op (eff : effs1) (sl : sr1) (sl : sr2) x
    -- run :: forall effs sr2 p q u t a .
    --   IProg (Op (Array: IIO: effs)) IVoid (p: sr2) (q: u: t) a ->
    --   IProg (Op (IIO: effs)) IVoid sr2 (u: t) a
    -- -- run :: forall effs p q u s t a .
    -- --   IProg (Op (Array: IIO: effs)) IVoid (p: u: s) (q: u: t) a ->
    -- --   IProg (Op (IIO: effs)) IVoid (u: s) (u: t) a
    -- run = runSerialArrays
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

embedIO1 :: IO a -> IProg (Op (IIO : effs)) IVoid (u : s) (u: s) a
embedIO1 io = Impure (OHere $ RunIO io) emptyCont

data Phantom a = Phantom Int

t1 :: Phantom (a:b:c) -> Phantom (a:b:c)
t1 = undefined


m1 :: (Phantom (a:rest) -> Phantom (a:rest)) -> Phantom (a:rest)
m1 = undefined

e1 = m1 t1