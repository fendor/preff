{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE TypeFamilyDependencies #-}

module Utils where

import qualified Prelude as P
import Data.Kind (Constraint, Type)
import GHC.TypeLits hiding (Nat)
import Prelude hiding (Monad (..), Applicative(..))
import Unsafe.Coerce

-- ------------------------------------------------
-- Main Effect monad
-- ------------------------------------------------

type f ~> g = forall x . f x -> g x

class IHFunctor h where
  ihmap :: (IFunctor f , IFunctor g) => (f p q ~> g q r) -> (h (f p q) ~> h (g q r))

class IHFunctor sig => Syntax sig where
  iemap :: (IMonad m) => (m p q a -> m p q b) -> (sig (m p q) a -> sig (m p q) b)
  iweave :: (IMonad m, IMonad n, Functor c) => c () -> (forall x . c (m p q x) -> n p q (c x)) -> (sig (m p q) a -> sig (n p q) (c a))

-- type IProg :: forall k.
--   (k -> k -> Type -> Type) ->
--   ((k -> k -> Type -> Type) -> k -> k -> k -> k -> Type -> Type -> Type) ->
--   k ->
--   k ->
--   Type ->
--   Type
data IProg f g p q a where
  Pure :: a -> IProg f g p p a
  Impure ::
    Op f p q x ->
    IKleisliTupled (IProg f g) '(q, x) '(r, a) ->
    -- (x -> IProg f g q r a)
    IProg f g p r a
  Scope ::
    g (IProg f g) p p' q' q x x' ->
    -- IProg f g p' q' x ->
    IKleisliTupled (IProg f g) '(q, x') '(r, a) ->
    -- (x' -> IProg f g q r a) ->
    IProg f g p r a

instance Functor (IProg f g p q) where
  fmap f (Pure a) = Pure $ f a
  fmap f (Impure op k) = Impure op (IKleisliTupled $ fmap f . runIKleisli k)
  fmap f (Scope op k) = Scope op (IKleisliTupled $ fmap f . runIKleisli k)

instance IFunctor (IProg f g) where
  imap f (Pure a) = Pure $ f a
  imap f (Impure op k) = Impure op (IKleisliTupled $ imap f . runIKleisli k)
  imap f (Scope op k) = Scope op (IKleisliTupled $ imap f . runIKleisli k)

instance IApplicative (IProg f g) where
  pure = Pure
  (Pure f) <*> k = fmap f k
  (Impure fop k') <*> k = Impure fop (IKleisliTupled $ (<*> k) . runIKleisli k')
  Scope fop k' <*> k = Scope fop (IKleisliTupled $ (<*> k) . runIKleisli k')

instance IMonad (IProg f g) where
  return :: a -> IProg f g i i a
  return = Pure

  (>>=) :: IProg f g i j a -> (a -> IProg f g j k b) -> IProg f g i k b
  (Pure a) >>= f = f a
  (Impure o k) >>= f = Impure o $ (IKleisliTupled $ (>>= f) . runIKleisli k)
  (Scope g k) >>= f = Scope g (IKleisliTupled $ (>>= f) . runIKleisli k)

type family Fst x where
  Fst '(a, b) = a
type family Snd x where
  Snd '(a, b) = b

-- | Wrapper type that can carry additional type state.
--
-- >>> :t runIKleisli (undefined :: IKleisliTupled m '(p, a) '(q, b))
-- runIKleisli (undefined :: IKleisliTupled m '(p, a) '(q, b))
--   :: forall k1 k2 k3 (p :: k1) a (m :: k1 -> k2 -> k3 -> *) (q :: k2)
--             (b :: k3).
--      a -> m p q b
--
-- >>> :t runIKleisli (undefined :: IKleisliTupled (Sem f) '(p, a) '(q, b))
-- runIKleisli (undefined :: IKleisliTupled (Sem f) '(p, a) '(q, b)) :: forall k p a (f :: [k -> k -> * -> *]) q b. a -> Sem f p q b
newtype IKleisliTupled m ia ob = IKleisliTupled
  { runIKleisli :: Snd ia -> m (Fst ia) (Fst ob) (Snd ob)
  }

(|>) :: IMonad m => IKleisliTupled m i o -> IKleisliTupled m o o2 -> IKleisliTupled m i o2
g |> f = IKleisliTupled $ \i -> runIKleisli g i >>= runIKleisli f

pure :: IMonad m => IKleisliTupled m '(p, x) '(p, x)
pure = IKleisliTupled Utils.return

transformKleisli ::
  (m (Fst ia) (Fst ob1) (Snd ob1) -> m (Fst ia) (Fst ob2) (Snd ob2))
  -> IKleisliTupled m ia ob1
  -> IKleisliTupled m ia ob2
transformKleisli f k = IKleisliTupled $ f . runIKleisli k

-- Less general instance, note the entries sl and sr in the type level list
type Op :: forall k.
  [k -> k -> Type -> Type] ->
  [k] ->
  [k] ->
  Type ->
  Type
data Op effs t1 t2 x where
  OHere ::
    forall x f1 effs sl1 sl2 sr .
    f1 sl1 sl2 x ->
    Op (f1 : effs) (sl1 ': sr) (sl2 ': sr) x
  OThere ::
    forall x eff effs sr1 sr2 sl .
    Op effs sr1 sr2 x ->
    Op (eff : effs) (sl ': sr1) (sl ': sr2) x

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
  SInl ::
    f1 p1 p2 q2 q1 x2 x1 ->
    (f1 :++: f2) '(p1, sr) '(p2, sr) '(q2, sr) '(q1, sr) x2 x1
  SInr ::
    f2 sp1 sp2 sq2 sq1 x2 x1 ->
    (f1 :++: f2) '(sl, sp1) '(sl, sp2) '(sl, sq2) '(sl, sq1) x2 x1

type IVoid :: forall k.
  (k -> k -> Type -> Type) ->
  k -> k -> k -> k -> Type -> Type -> Type
data IVoid m p p' q' q x x'

runI :: IProg '[IIdentity] IVoid '[()] '[()] a -> a
runI (Pure a) = a
runI (Impure (OHere cmd) k) = runI $ unsafeCoerce runIKleisli k (runIdentity cmd)
runI (Impure (OThere _) _k) = error "Impossible"
runI (Scope _ _) = error "Impossible"

run :: IProg '[] IVoid '[] '[] a -> a
run (Pure a) = a
run (Impure _ _) = error "Impossible"
run (Scope _ _) = error "Impossible"

-- ------------------------------------------------
-- Sem Monad and Simple Runners
-- ------------------------------------------------

newtype IIdentity p q a = IIdentity a

runIdentity :: IIdentity p q a -> a
runIdentity (IIdentity a) = a

type IIO :: forall k. k -> k -> Type -> Type
data IIO p q a where
  RunIO :: IO a -> IIO p p a

runIO :: IProg '[IIO] IVoid p q a -> IO a
runIO (Pure a) = P.pure a
runIO (Impure (OHere (RunIO a)) k) = a P.>>= \x ->runIO $ runIKleisli k x
runIO (Impure (OThere _) _k) = error "Impossible"
runIO (Scope _ _) = error "Impossible"

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

type family FindEff e effs :: Natural where
  FindEff e '[] = TypeError (Text "Not found")
  FindEff e (e  ': eff) = 0
  FindEff e (e' ': eff) = 1 + FindEff e eff

type family Write ind p ps where
  Write _ _ '[]      = TypeError (Text "This sucks")
  Write 0 p (x : xs) = p : xs
  Write n p (x : xs) = x : Write (n - 1) p xs

type family Assume ind ps where
  Assume _ '[]      = TypeError (Text "This sucks")
  Assume 0 (x : xs) = x
  Assume n (x : xs) = Assume (n - 1) xs

inj :: KnownNat n =>
  proxy n -> e p q a -> Op effs ps qs a
inj pval op = go (natVal pval)
  where
    -- go :: Integer -> Op (e : effs2) (p : ps2) (q : qs2) a
    go 0 = unsafeCoerce OHere op
    go n = unsafeCoerce OThere (go (n - 1))


-- class SMember e effs pres posts where
--   inj :: e () () a -> Op effs pres posts a

-- instance {-# OVERLAPPING #-} SMember e (e ': effs) (() ': ps) (() ': qs) where
--   -- inj ::
--   --   e () () a ->
--   --   Op (e ': effs) (() ': ps) (() ': ps) a
--   inj e = OHere e

-- instance {-# INCOHERENT #-} SMember e effs ps qs => SMember e (eff ': effs) (s ': ps) (t ': qs) where
--   inj = OThere . inj

-- instance
--   TypeError (Text "Failed to resolve effect " :<>: ShowType e :$$:
--              Text "Perhaps check the type of effectful computation and the sequence of handlers for concordance?"
--             )
--   => SMember e '[] '[] '[] where
--     inj = error "The instance of SMember e p q '[] '[] '[] must never be selected"


-- class CMember e p q effs pres posts where
--   injC :: e p q a -> Op effs pres posts a

-- instance {-# OVERLAPPING #-} CMember e p q (e ': effs) (p ': ps) (q ': qs) where
--   injC ::
--     e p q a ->
--     Op (e ': effs) (p ': ps) (q ': qs) a
--   injC e = OHere e

-- instance {-# INCOHERENT #-} CMember e p q effs ps qs => CMember e p q (eff ': effs) (s ': ps) (t ': qs) where
--   injC = OThere . injC

-- instance
--   TypeError (Text "Failed to resolve effect " :<>: ShowType e :$$:
--              Text "Perhaps check the type of effectful computation and the sequence of handlers for concordance?"
--             )
--   => CMember e p q '[] '[] '[] where
--     injC = error "The instance of SMember e p q '[] '[] '[] must never be selected"

-- class Test a b where
--   output :: a -> b -> String

-- instance Test a b where
--   output _ _ = "Same"

-- instance Test a b where
--   output _ _ = "Different"


-- | Find the index of an element in a type-level list.
-- The element must exist
-- This is essentially a compile-time computation.
-- Using overlapping instances here is OK since this class is private to this
-- module
-- class FindElem e p q effs pres posts where
--   inj' :: e p q a -> Op effs pres posts a

-- instance FindElem t (t ': r) where
--   inj' = Here e
-- instance {-# OVERLAPPABLE #-} FindElem t r => FindElem t (t' ': r) where
--   inj' = There . inj'
-- instance TypeError ('Text "Cannot unify effect types." ':$$:
--                     'Text "Unhandled effect: " ':<>: 'ShowType t ':$$:
--                     'Text "Perhaps check the type of effectful computation and the sequence of handlers for concordance?")
--   => FindElem e p q '[] '[] '[] where
--   inj' = error "unreachable"

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
