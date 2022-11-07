{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE TypeFamilyDependencies #-}

module Utils where

import Data.Kind (Constraint, Type)
import GHC.TypeLits hiding (Nat)
import Prelude hiding (Monad (..), Applicative(..))
import qualified Prelude as P

-- ------------------------------------------------
-- Main Effect monad
-- ------------------------------------------------

type f ~> g = forall x . f x -> g x

class IHFunctor h where
  ihmap :: (IFunctor f , IFunctor g) => (f p q ~> g q r) -> (h (f p q) ~> h (g q r))

class IHFunctor sig => Syntax sig where
  iemap :: (IMonad m) => (m p q a -> m p q b) -> (sig (m p q) a -> sig (m p q) b)
  iweave :: (IMonad m, IMonad n, Functor c) => c () -> (forall x . c (m p q x) -> n p q (c x)) -> (sig (m p q) a -> sig (n p q) (c a))

type IProg :: forall k.
  (k -> k -> Type -> Type) ->
  (k -> k -> k -> k -> Type -> Type -> Type) ->
  k ->
  k ->
  Type ->
  Type
data IProg f g p q a where
  Pure :: a -> IProg f g p p a
  Impure ::
    f p q x ->
    IKleisliTupled (IProg f g) '(q, x) '(r, a) ->
    -- (x' -> IProg f g q r a)
    IProg f g p r a
  Scope ::
      g p p' q' q x x' ->
      IProg f g p' q' x ->
      (x' -> IProg f g q r a) ->
      IProg f g p r a

instance Functor (IProg f g p q) where
  fmap f (Pure a) = Pure $ f a
  fmap f (Impure op k) = Impure op (IKleisliTupled $ fmap f . runIKleisliTupled k)
  fmap f (Scope op prog k) = Scope op prog (fmap (fmap f) k)

instance IFunctor (IProg f g) where
  imap f (Pure a) = Pure $ f a
  imap f (Impure op k) = Impure op (IKleisliTupled $ imap f . runIKleisliTupled k)
  imap f (Scope op prog k) = Scope op prog (fmap (imap f) k)

instance IApplicative (IProg f g) where
  pure = Pure
  (Pure f) <*> k = fmap f k
  (Impure fop k') <*> k = Impure fop (IKleisliTupled $ (<*> k) . runIKleisliTupled k')
  Scope fop prog k' <*> k = Scope fop prog (fmap (<*> k) k')

instance IMonad (IProg f g) where
  return :: a -> IProg f g i i a
  return = Pure

  (>>=) :: IProg f g i j a -> (a -> IProg f g j k b) -> IProg f g i k b
  (Pure a) >>= f = f a
  (Impure o a) >>= f = Impure o $ (IKleisliTupled $ (>>= f) . runIKleisliTupled a)
  (Scope g c a) >>= f = Scope g c (fmap (>>= f) a)

type family Fst x where
  Fst '(a, b) = a
type family Snd x where
  Snd '(a, b) = b

-- | Wrapper type that can carry additional type state.
--
-- >>> :t runIKleisliTupled (undefined :: IKleisliTupled m '(p, a) '(q, b))
-- runIKleisliTupled (undefined :: IKleisliTupled m '(p, a) '(q, b))
--   :: forall k1 k2 k3 (p :: k1) a (m :: k1 -> k2 -> k3 -> *) (q :: k2)
--             (b :: k3).
--      a -> m p q b
--
-- >>> :t runIKleisliTupled (undefined :: IKleisliTupled (Sem f) '(p, a) '(q, b))
-- runIKleisliTupled (undefined :: IKleisliTupled (Sem f) '(p, a) '(q, b)) :: forall k p a (f :: [k -> k -> * -> *]) q b. a -> Sem f p q b
newtype IKleisliTupled m ia ob = IKleisliTupled
  { runIKleisliTupled :: Snd ia -> m (Fst ia) (Fst ob) (Snd ob)
  }

(|>) :: IMonad m => IKleisliTupled m i o -> IKleisliTupled m o o2 -> IKleisliTupled m i o2
g |> f = IKleisliTupled $ \i -> runIKleisliTupled g i >>= runIKleisliTupled f

emptyCont :: IMonad m => IKleisliTupled m '(p, x) '(p, x)
emptyCont = IKleisliTupled Utils.return

transformKleisli ::
  (m (Fst ia) (Fst ob1) (Snd ob1) -> m (Fst ia) (Fst ob2) (Snd ob2))
  -> IKleisliTupled m ia ob1
  -> IKleisliTupled m ia ob2
transformKleisli f k = IKleisliTupled $ f . runIKleisliTupled k

infixr 5 :+:
type (:+:) ::
  forall sl sr.
  (sl -> sl -> Type -> Type) ->
  (sr -> sr -> Type -> Type) ->
  (sl, sr) ->
  (sl, sr) ->
  Type ->
  Type
data (f1 :+: f2) t1 t2 x where
  OInl :: f1 sl1 sl2 x -> (f1 :+: f2) '(sl1, sr) '(sl2, sr) x
  OInr :: f2 sr1 sr2 x -> (f1 :+: f2) '(sl, sr1) '(sl, sr2) x

infixr 5 :++:
type (:++:) ::
  forall sl sr.
  (sl -> sl -> sl -> sl -> Type -> Type -> Type) ->
  (sr -> sr -> sr -> sr -> Type -> Type -> Type) ->
  (sl, sr) ->
  (sl, sr) ->
  (sl, sr) ->
  (sl, sr) ->
  Type ->
  Type ->
  Type
data (f1 :++: f2) p1 p2 q2 q1 x2 x1 where
  SInl :: f1 p1 p2 q2 q1 x2 x1 -> (f1 :++: f2) '(p1, sr) '(p2, sr) '(q2, sr) '(q1, sr) x2 x1
  SInr :: f2 sp1 sp2 sq2 sq1 x2 x1 -> (f1 :++: f2) '(sl, sp1) '(sl, sp2) '(sl, sq2) '(sl, sq1) x2 x1

-- TODO: Use this eventually again
type Ops :: forall k . [k -> k -> Type -> Type] -> k -> k -> Type -> Type
data Ops fs p q x where
  Here :: f s t x -> Ops (f : fs) (s, p) (t, q) x
  There :: Ops fs s t x -> Ops (f : fs) (p, s) (q, t) x

-- ------------------------------------------------
-- Sem Monad and Simple Runners
-- ------------------------------------------------


instance IMonad (Sem f) where
  return :: a -> Sem f i i a
  return = Value

  (>>=) :: Sem f i j a -> (a -> Sem f j k b) -> Sem f i k b
  (Value a) >>= f = f a
  (Op o a) >>= f = Op o (a |> IKleisliTupled f)

type Sem ::
  (k -> k -> Type -> Type) ->
  k ->
  k ->
  Type ->
  Type
data Sem f p q a where
  Value :: a -> Sem f p p a
  Op ::
    f p q x ->
    IKleisliTupled (Sem f) '(q, x) '(r, a) ->
    -- x -> Sem f q r a
    Sem f p r a

runPure
  :: (forall j p b. f j p b -> b)
  -> Sem (f :+: fs) '(i, is) '(o, os) a
  -> Sem fs is os a
runPure _ (Value a) = Value a
runPure f (Op (OInr cmd) q) = Op cmd k
  where k = IKleisliTupled $ \a -> runPure f $ runIKleisliTupled q a
runPure f (Op (OInl cmd) q) = runPure f $ runIKleisliTupled q (f cmd)

newtype IIdentity p q a = IIdentity a

runIdentity :: IIdentity p q a -> a
runIdentity (IIdentity a) = a

run :: Sem IIdentity p q a -> a
run (Value a) = a
run (Op cmd k) = run $ runIKleisliTupled k (runIdentity cmd)

data IIO p q a where
  RunIO :: IO a -> IIO p p a

runIO :: Sem IIO p q a -> IO a
runIO (Value a) = P.pure a
runIO (Op (RunIO io) k) = io P.>>= runIO . runIKleisliTupled k

-- TODO: not general enough
embedIO :: IO a -> Sem (f :+: IIO) '(p1, q1) '(p1, q1) a
embedIO act = Op (OInr $ RunIO act) (IKleisliTupled return)

embedIO1 :: IO a -> Sem IIO q q a
embedIO1 act = Op (RunIO act) (IKleisliTupled return)
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

type RemoveLast :: [a] -> [a]
type family RemoveLast xs where
  RemoveLast '[] = TypeError (Text "Tried to remove last element from empty list")
  RemoveLast (x ': '[]) = '[]
  RemoveLast (x ': xs) = x : RemoveLast xs

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

-- ------------------------------------------------
-- Rebindable Syntax and IMonad Utils
-- ------------------------------------------------

ifThenElse :: Bool -> p -> p -> p
ifThenElse True a _ = a
ifThenElse False _ b = b

when :: (IMonad m) => Bool -> m i i () -> m i i ()
when False _ = return ()
when True a = a

foldM :: (IMonad m) => [a] -> c -> (a -> c -> m i i c) -> m i i c
foldM [] c _f = return c
foldM [x] c f =
  f x c
foldM (x : xs) c f =
  f x c >>= \c' -> foldM xs c' f
