{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -Wno-missing-signatures #-}
module Parameterised.Array where
import Utils
import Prelude hiding (Monad(..))
import Parameterised.State (Future(..))

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
    Array p (Replace (Replace (Replace p n1 N) n2 N) k X) ()
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


data Thread p p' q' q x x' where
  AFork :: (AcceptableList p1 q1 p2) => Thread p1 p2 q2 q1 a (Future a)
  AFinish :: Thread p p q p () ()

afork s = Scope AFork s return
afinish s = Scope AFinish s return
join i1 i2 = Impure (Join i1 i2) return
write a b c = Impure (Write a b c) return
malloc a b = Impure (Malloc a b) return
slice a b = Impure (Split a b) return
length a = Impure (Length a) return
read a b = Impure (Read a b) return
wait a = Impure (Wait a) return
injectIO a = Impure (InjectIO a) return
