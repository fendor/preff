{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneKindSignatures #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -Wno-missing-signatures #-}

module Utils where

import Data.Kind (Constraint, Type)
import GHC.TypeLits (ErrorMessage (..), TypeError)
import Prelude hiding (Monad (..))

data Nat = Z | S Nat

type Lookup :: [a] -> Nat -> a
type family Lookup a b where
  Lookup '[] _ = TypeError (Text "Could not find index")
  Lookup (_ ': xs) (S n) = Lookup xs n
  Lookup (x ': _) Z = x

type Replace :: [m] -> Nat -> m -> [m]
type family Replace xs idx m where
  Replace (x ': xs) Z m = m ': xs
  Replace (x ': xs) (S s) m = x ': (Replace xs s m)

type Append :: [a] -> a -> [a]
type family Append xs x where
  Append '[] t = t ': '[]
  Append (x ': xs) t = x ': (Append xs t)

type Length :: [a] -> Nat
type family Length a where
  Length '[] = Z
  Length (x ': xs) = S (Length xs)

data IProg f g p q a where
  Pure :: a -> IProg f g p p a
  Impure :: f p q a -> (a -> IProg f g q r b) -> IProg f g p r b
  Scope :: g p p' q' q x x' -> IProg f g p' q' x -> (x' -> IProg f g q r a) -> IProg f g p r a

type (≠) :: forall a. a -> a -> Bool
type family (≠) a b where
  a ≠ a = False
  a ≠ b = True

type a ≁ b = (a ≠ b) ~ True

type Operation a = a -> a -> Type -> Type
type Scope a = a -> a -> a -> a -> Type -> Type -> Type

type IMonad :: (p -> p -> Type -> Type) -> Constraint
class IMonad m where
  return :: a -> m i i a
  (>>=) :: m i j a -> (a -> m j k b) -> m i k b
  (>>) :: m i j a -> m j k b -> m i k b
  g >> f = g >>= const f

type Apply :: forall k a. k a -> a -> a
type family Apply a b
type Reverse :: forall k a. k a -> a -> a -> a
type family Reverse a b c

type Map :: forall k a. k a -> [a] -> [a]
type family Map f a where
  Map f '[] = '[]
  Map f (x ': xs) = (Apply f x) ': (Map f xs)

type MapReverse :: forall k a. k a -> [a] -> [a] -> [a]
type family MapReverse f a b where
  MapReverse f '[] _ = '[]
  MapReverse f (x ': xs) (y ': ys) = (Reverse f x y) ': (MapReverse f xs ys)

type Take :: [a] -> Nat -> [a]
type family Take xs n where
  Take _ Z = '[]
  Take (x ': xs) (S n) = x ': (Take xs n)

instance IMonad (IProg f g) where
  return :: a -> IProg f g i i a
  return = Pure

  (>>=) :: IProg f g i j a -> (a -> IProg f g j k b) -> IProg f g i k b
  (Pure a) >>= f = f a
  (Impure o a) >>= f = Impure o $ fmap (>>= f) a
  (Scope g c a) >>= f = Scope g c (fmap (>>= f) a)

data AccessLevel = N | R | X

--data Container = Contains AccessLevel
type Acceptable :: AccessLevel -> AccessLevel -> AccessLevel -> Constraint
class Acceptable a b c | a b -> c, a c -> b
instance Acceptable X X N
instance Acceptable X N X
instance Acceptable X R R
instance Acceptable R R R
instance Acceptable N N N

type AcceptableList :: [AccessLevel] -> [AccessLevel] -> [AccessLevel] -> Constraint
class AcceptableList as bs cs
instance AcceptableList '[] '[] '[]
instance (Acceptable a b c, AcceptableList as bs cs) => AcceptableList (a ': as) (b ': bs) (c ': cs)

data StateF p q x where
  Alloc :: t -> StateF p (Append p X) (Token t (Length p))
  Get ::
    (R ≤ (Lookup p n)) =>
    Token t n ->
    StateF p p t
  Put ::
    (X ≤ (Lookup p n)) =>
    Token t n ->
    t ->
    StateF p p ()

data StateG p p' q' q x x' where
  Fork :: (AcceptableList p1 q1 p2) => StateG p1 p2 q2 q1 a (Future a)
  Finish :: StateG p p q p a a

type Token :: Type -> Nat -> Type
newtype Token t n = Token ()
data Future a = Future

put a b = Impure (Put a b) return
alloc a = Impure (Alloc a) return
get a = Impure (Get a) return
fork s = Scope Fork s return
finish s = Scope Finish s return

type Msg = Text "You could be writing to a resource, you have no access to."

type (≤) :: AccessLevel -> AccessLevel -> Constraint
class a ≤ b
instance a ≤ X
instance R ≤ R
instance N ≤ R
instance N ≤ N
instance TypeError Msg => X ≤ N

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

type Max :: AccessLevel -> AccessLevel -> AccessLevel
type family Max a b where
  Max X _ = X
  Max _ X = X
  Max R _ = R
  Max _ R = R
  Max _ _ = N
