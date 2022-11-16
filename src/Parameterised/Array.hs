{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -Wno-missing-signatures #-}

module Parameterised.Array where

import Control.Concurrent.STM
import Data.Array.IO as IO
import GHC.Types (Any)
import Parameterised.State (Future (..))
import Unsafe.Coerce (unsafeCoerce)
import Utils
import Prelude hiding (Monad (..), read)
import qualified Prelude as P
import Data.Kind

data ValueType where
  Actual :: ValueType
  Slice :: Nat -> ValueType

--newtype AToken t v n = AToken ()
data AToken t v n where
  AToken :: a -> AToken t v n

data Array p q x where
  Split ::
    (X ≤ Lookup p n, k ~ Length p) =>
    AToken t v n ->
    Int ->
    Array
      p
      (Append (Append (Replace p n N) X) X)
      (AToken t (Slice n) k, AToken t (Slice n) (S k))
  Join ::
    (X ≤ Lookup p n1, X ≤ Lookup p n2, Lookup p k ~ N) =>
    AToken t (Slice k) n1 ->
    AToken t (Slice k) n2 ->
    Array p (Replace (RemoveLast (RemoveLast p)) k X) ()
  Malloc ::
    Int ->
    t ->
    Array p (Append p X) (AToken t Actual (Length p))
  Write ::
    (X ≤ Lookup p n) =>
    AToken t v n ->
    Int ->
    t ->
    Array p p ()
  Read ::
    (R ≤ Lookup p n) =>
    AToken t v n ->
    Int ->
    Array p p t
  Length ::
    (R ≤ Lookup p n) =>
    AToken t v n ->
    Array p p Int
  Wait ::
    Future a ->
    Array p p a
  InjectIO ::
    IO a ->
    Array p p a

-- type Thread :: forall k .
--   (k -> k -> Type -> Type) ->
--    k -> k -> k -> k -> Type -> Type ->
--   Type

data Thread m p p' q' q x x' where
  AFork :: (AcceptableList p1 q1 p2) => m p2 q2 a -> Thread m p1 p2 q2 q1 a (Future a)
  AFinish :: m p q () -> Thread m p p q p () ()

-- afork :: AcceptableList p r p' => IProg f Thread p' q' x -> IProg f Thread p r (Future x)
afork s = Scope (AFork s) emptyCont

afinish s = Scope (AFinish s) emptyCont

join i1 i2 = Impure (OHere $ Join i1 i2) emptyCont

write a b c = Impure (OHere $ Write a b c) emptyCont

malloc a b = Impure (OHere $ Malloc a b) emptyCont

slice a b = Impure (OHere $ Split a b) emptyCont

length a = Impure (OHere $ Length a) emptyCont

read a b = Impure (OHere $ Read a b) emptyCont

wait a = Impure (OHere $ Wait a) emptyCont

injectIO a = Impure (OHere $ InjectIO a) emptyCont

-- ----------------------------------------------------------
-- IO Runner for parallel arrays
-- ----------------------------------------------------------

type Bounds = (Int, Int)

unsafeCreate :: forall a t v n. a -> AToken t v n
unsafeCreate = AToken

unsafeUncover :: forall a t v n. AToken t v n -> a
unsafeUncover (AToken a) = unsafeCoerce a

unsafeCreateA :: forall k1 k2 k3 (t :: k1) (v :: k2) (n :: k3). (Bounds, IO.IOArray Int Any) -> AToken t v n
unsafeCreateA = unsafeCreate @(Bounds, IO.IOArray Int Any)

unsafeUncoverA :: forall k1 k2 k3 (t :: k1) (v :: k2) (n :: k3). AToken t v n -> (Bounds, IO.IOArray Int Any)
unsafeUncoverA = unsafeUncover @(Bounds, IO.IOArray Int Any)

-- serialExample :: IProg Array any '[] '[X] Integer
-- serialExample = do
--   arr <- malloc 5 0
--   write arr 0 1
--   val <- read arr 0
--   return val


runArrays ::
  IProg '[Array] Thread '[p] '[q] a ->
  IO ()
runArrays prog = runArraysH prog P.>> P.return ()

runArraysH :: forall (p :: [AccessLevel]) (q :: [AccessLevel]) a.
  IProg '[Array] Thread '[p] '[q] a ->
  IO [TMVar ()]
runArraysH (Pure _a) = P.return []
runArraysH (Impure (OHere (Malloc i (a :: b))) c) =
  let upper = i - 1
   in let bounds = (0, upper)
       in (IO.newArray bounds a :: IO (IO.IOArray Int b))
            P.>>= ( \arr ->
                      let arr' = (unsafeCoerce arr :: IO.IOArray Int Any)
                       in runArraysH (runIKleisliTupled c (unsafeCreateA (bounds, arr')))
                  )
runArraysH (Impure (OHere (Read n i)) c) =
  let ((lower, upper), arr) = unsafeUncoverA n
   in let offset = i + lower
       in if offset > upper || offset < lower
            then error $ "Index out of bounds " ++ show (lower, upper) ++ " " ++ show i
            else
              IO.readArray (arr :: IO.IOArray Int Any) offset
                P.>>= (\v -> v `seq` runArraysH (runIKleisliTupled c (unsafeCoerce v)))
runArraysH (Impure (OHere (Write n i (a :: b))) c) =
  let ((lower, upper), arr) = unsafeUncoverA n
   in let offset = i + lower
       in if offset > upper || offset < lower
            then error "Index out of bounds"
            else
              IO.writeArray (unsafeCoerce arr :: IO.IOArray Int b) offset a
                P.>>= (\v -> v `seq` runArraysH (runIKleisliTupled c ()))
runArraysH (Impure (OHere (Length n)) c) =
  let ((lower, upper), _arr) = unsafeUncoverA n
   in if upper - lower + 1 < 0
        then error "Should not be here"
        else runArraysH (runIKleisliTupled c (upper - lower + 1))
runArraysH (Impure (OHere (Join _a _b)) c) =
  runArraysH (runIKleisliTupled c ())
runArraysH (Impure (OHere (Split n i)) c) =
  let ((lower, upper), arr) = unsafeUncoverA n
   in let offset = i + lower
       in if offset > upper || offset < lower
            then error ("Index out of bounds " ++ show i ++ " " ++ show (lower, upper))
            else
              let n1 = (lower, offset)
               in let n2 = (offset + 1, upper)
                   in runArraysH (runIKleisliTupled c (unsafeCreateA (n1, arr), unsafeCreateA (n2, arr)))
runArraysH (Impure (OHere (InjectIO a)) c) =
  a P.>>= (runArraysH . runIKleisliTupled c)
runArraysH (Scope (AFork c) a) =
  newEmptyTMVarIO
    P.>>= ( \var {-forkIO ( -} ->
              runArraysH c
                P.>>= (atomically . mapM_ takeTMVar)
                  P.>> atomically (putTMVar var () {-)-})
                  P.>> runArraysH (runIKleisliTupled a Future)
                P.>>= (\result -> P.return (var : result))
          )
runArraysH (Scope (AFinish c) a) =
  undefined
  -- runArraysH c P.>>= (atomically . mapM_ takeTMVar) P.>> runArraysH (runIKleisliTupled a ())
runArraysH _ = undefined
