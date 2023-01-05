{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -Wno-missing-signatures #-}

module MiniEff.Parameterised.Array where

import Control.Concurrent.STM
import Data.Array.IO as IO
import GHC.Types (Any)
import MiniEff.Parameterised.State (Future (..))
import Unsafe.Coerce (unsafeCoerce)
import MiniEff
import qualified Control.IxMonad as Ix
import Prelude hiding (Monad (..), read)
import qualified Prelude as P

data ValueType where
  Actual :: ValueType
  Slice :: Nat -> ValueType

{- | @'AToken' t v n@
 * @t@ is the type we contain
 * @v@ is the valuetype
 * @n@ is the index in the AccessList
-}
data AToken t v n where
  AToken :: a -> AToken t v n

-- type Array :: forall k. [AccessLevel] -> [AccessLevel] -> Type -> Type
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
--   ([[AccessLevel]] -> [[AccessLevel]] -> Type -> Type) ->
--    [[AccessLevel]] -> [[AccessLevel]] -> [[AccessLevel]] -> [[AccessLevel]] -> Type -> Type ->
--   Type

data instance ScopeE Array m p p' q' q x x' where
  AFork ::
    (AcceptableList p1 q1 p2) =>
    m p2 q2 a ->
    ScopeE Array m p1 p2 q2 q1 a (Future a)
  -- TODO: sr1 ~ [] is required for the runner
  AFinish :: m p q () -> ScopeE Array m p p q p () ()

-- afork :: AcceptableList p r p' => MiniEff f Thread p' q' x -> MiniEff f Thread p r (Future x)
afork s = ScopedP (AFork s) emptyCont

afinish s = ScopedP (AFinish s) emptyCont

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

runArrays ::
  MiniEff '[IIO] Array p q a ->
  IO ()
runArrays prog = P.do
  _ <- runIO $ runArraysH prog
  P.pure ()

runArraysH ::
  Member IIO effs =>
  MiniEff effs Array p q a ->
  MiniEff effs IVoid () () [TMVar ()]
runArraysH (Value _a) = Ix.return []
runArraysH (ImpureP (Malloc i (a :: b)) c) =
  let upper = i - 1
   in let bounds = (0, upper)
       in Ix.do
            arr <- embedIO $ (IO.newArray bounds a :: IO (IO.IOArray Int b))
            let arr' = (unsafeCoerce arr :: IO.IOArray Int Any)
            runArraysH (runIKleisliTupled c (unsafeCreateA (bounds, arr')))
runArraysH (ImpureP ((Read n i)) c) =
  let ((lower, upper), arr) = unsafeUncoverA n
   in let offset = i + lower
       in if offset > upper || offset < lower
            then error $ "Index out of bounds " ++ show (lower, upper) ++ " " ++ show i
            else
              embedIO (IO.readArray (arr :: IO.IOArray Int Any) offset)
                Ix.>>= (\v -> v `seq` runArraysH (runIKleisliTupled c (unsafeCoerce v)))
runArraysH (ImpureP ((Write n i (a :: b))) c) =
  let ((lower, upper), arr) = unsafeUncoverA n
   in let offset = i + lower
       in if offset > upper || offset < lower
            then error "Index out of bounds"
            else
              embedIO (IO.writeArray (unsafeCoerce arr :: IO.IOArray Int b) offset a)
                Ix.>>= (\v -> v `seq` runArraysH (runIKleisliTupled c ()))
runArraysH (ImpureP ((Length n)) c) =
  let ((lower, upper), _arr) = unsafeUncoverA n
   in if upper - lower + 1 < 0
        then error "Should not be here"
        else runArraysH (runIKleisliTupled c (upper - lower + 1))
runArraysH (ImpureP ((Join _a _b)) c) =
  runArraysH (runIKleisliTupled c ())
runArraysH (ImpureP ((Split n i)) c) =
  let ((lower, upper), arr) = unsafeUncoverA n
   in let offset = i + lower
       in if offset > upper || offset < lower
            then error ("Index out of bounds " ++ show i ++ " " ++ show (lower, upper))
            else
              let n1 = (lower, offset)
               in let n2 = (offset + 1, upper)
                   in runArraysH (runIKleisliTupled c (unsafeCreateA (n1, arr), unsafeCreateA (n2, arr)))
runArraysH (ImpureP ((InjectIO a)) c) = Ix.do
  v <- embedIO a
  runArraysH $ runIKleisliTupled c v
runArraysH (ScopedP (AFork c) a) = Ix.do
  var <- embedIO newEmptyTMVarIO

  runArraysH c
    Ix.>>= \x ->
      embedIO (atomically $ mapM_ takeTMVar x)
        Ix.>> embedIO (atomically (putTMVar var () {-)-}))
        Ix.>> runArraysH (runIKleisliTupled a Future)
        Ix.>>= (\result -> Ix.return (var : result))
runArraysH (ScopedP (AFinish c) a) =
  runArraysH c Ix.>>= (embedIO . atomically . mapM_ takeTMVar) Ix.>> runArraysH (runIKleisliTupled a ())
runArraysH _ = undefined
