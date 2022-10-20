{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneKindSignatures #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}

module Utils where

import Data.Kind (Constraint, Type)
import GHC.TypeLits (ErrorMessage (..), TypeError)
import Prelude hiding (Monad (..), Applicative(..))
import Data.WorldPeace (Union)

-- ------------------------------------------------
-- Main Effect monad
-- ------------------------------------------------

type IProg :: forall k.
  (k -> k -> Type -> Type)
  -> (k -> k -> k -> k -> Type -> Type -> Type) -> k -> k -> Type -> Type
data IProg f g p q a where
  Pure :: a -> IProg f g p p a
  Impure :: f p q x -> (x -> IProg f g q r a) -> IProg f g p r a
  Scope :: g p p' q' q x x' -> IProg f g p' q' x -> (x' -> IProg f g q r a) -> IProg f g p r a

-- data ISem f g p q a where
--   Val :: a -> IProg f g p p a
--   Op :: OpenUnion x -> (x -> IProg f g q r a) -> IProg f g p r a

instance Functor (IProg f g p q) where
  fmap f (Pure a) = Pure $ f a
  fmap f (Impure op k) = Impure op (fmap (fmap f) k)
  fmap f (Scope op prog k) = Scope op prog (fmap (fmap f) k)

instance IFunctor (IProg f g) where
  imap f (Pure a) = Pure $ f a
  imap f (Impure op k) = Impure op (fmap (imap f) k)
  imap f (Scope op prog k) = Scope op prog (fmap (imap f) k)

instance IApplicative (IProg f g) where
  pure = Pure

  -- (<*>) :: forall k (f :: k -> k -> * -> *) (g :: k -> k -> k -> k -> * -> * -> *) (i :: k) (j :: k) a b.
  --     IProg f g i j (a -> b) -> IProg f g i j a -> IProg f g q r b
  (Pure f) <*> k = fmap f k
  (Impure fop k') <*> k = Impure fop (fmap (<*> k) k')
  Scope fop prog k' <*> k = Scope fop prog (fmap (<*> k) k')

instance IMonad (IProg f g) where
  return :: a -> IProg f g i i a
  return = Pure

  (>>=) :: IProg f g i j a -> (a -> IProg f g j k b) -> IProg f g i k b
  (Pure a) >>= f = f a
  (Impure o a) >>= f = Impure o $ fmap (>>= f) a
  (Scope g c a) >>= f = Scope g c (fmap (>>= f) a)

-- TODO: can we write this?
-- fold :: forall f g p q a b. IFunctor f => (f p q a -> b) -> (a -> b) -> (IProg f g p q a -> b)
-- fold _   gen (Pure x) = gen x
-- fold alg gen (Impure op k) = alg (imap (fold alg gen) op)
-- fold alg gen (Scope op prog k) = undefined


-- type (:+:) :: forall k . (k -> k -> Type -> Type) -> (k -> k -> Type -> Type) -> Type -> (k -> k -> Type -> Type)
data (:+:) f g s t a where
  Inl :: f p q a -> (f :+: g) p q a
  Inr :: g x y a -> (f :+: g) x y a

newtype IIdentity p q a = IIdentity a

runIdentity :: IIdentity p q a -> a
runIdentity (IIdentity a) = a

-- ------------------------------------------------
-- Parametric Effect monad
-- ------------------------------------------------

type IMonad :: (p -> p -> Type -> Type) -> Constraint
class IMonad m where
  return :: a -> m i i a
  (>>=) :: m i j a -> (a -> m j k b) -> m i k b
  (>>) :: m i j a -> m j k b -> m i k b
  g >> f = g >>= const f

type IFunctor :: (p -> p -> Type -> Type) -> Constraint
class IFunctor f where
  imap :: (a -> b) -> f p q a -> f p q b

class IFunctor f => IApplicative f where
  pure :: a -> f i i a
  (<*>) :: f i j (a -> b) -> f j r a -> f i r b

-- ------------------------------------------------
-- Effect System utilities
-- ------------------------------------------------

data Nat = Z | S Nat

type Lookup :: [a] -> Nat -> a
type family Lookup a b where
  Lookup '[] _ = TypeError (Text "Could not find index")
  Lookup (_ ': xs) (S n) = Lookup xs n
  Lookup (x ': _) Z = x

type Replace :: [m] -> Nat -> m -> [m]
type family Replace xs idx m where
  Replace (x ': xs) Z m = m ': xs
  Replace (x ': xs) (S s) m = x ': Replace xs s m

type Append :: [a] -> a -> [a]
type family Append xs x where
  Append '[] t = t ': '[]
  Append (x ': xs) t = x ': Append xs t

type Length :: [a] -> Nat
type family Length a where
  Length '[] = Z
  Length (x ': xs) = S (Length xs)

type (≠) :: forall a. a -> a -> Bool
type family (≠) a b where
  a ≠ a = False
  a ≠ b = True

type a ≁ b = (a ≠ b) ~ True

type Operation a = a -> a -> Type -> Type

type Scope a = a -> a -> a -> a -> Type -> Type -> Type

type Apply :: forall k a. k a -> a -> a
type family Apply a b

type Reverse :: forall k a. k a -> a -> a -> a
type family Reverse a b c

type Map :: forall k a. k a -> [a] -> [a]
type family Map f a where
  Map f '[] = '[]
  Map f (x ': xs) = Apply f x ': Map f xs

type MapReverse :: forall k a. k a -> [a] -> [a] -> [a]
type family MapReverse f a b where
  MapReverse f '[] _ = '[]
  MapReverse f (x ': xs) (y ': ys) = Reverse f x y ': MapReverse f xs ys

type Take :: [a] -> Nat -> [a]
type family Take xs n where
  Take _ Z = '[]
  Take (x ': xs) (S n) = x ': Take xs n

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

type Msg = Text "You could be writing to a resource, you have no access to."

type (≤) :: AccessLevel -> AccessLevel -> Constraint
class a ≤ b

instance a ≤ X

instance R ≤ R

instance N ≤ R

instance N ≤ N

instance TypeError Msg => X ≤ N

type Max :: AccessLevel -> AccessLevel -> AccessLevel
type family Max a b where
  Max X _ = X
  Max _ X = X
  Max R _ = R
  Max _ R = R
  Max _ _ = N
