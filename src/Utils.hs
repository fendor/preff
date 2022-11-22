{-# LANGUAGE TypeFamilyDependencies #-}
{-# LANGUAGE UndecidableInstances #-}

module Utils where

import Data.Kind (Constraint, Type)
import GHC.TypeLits hiding (Nat)
import Prelude hiding (Applicative (..), Monad (..))
import qualified Prelude as P

-- ------------------------------------------------
-- Main Effect monad
-- ------------------------------------------------

type IProg ::
  forall k.
  [Type -> Type] ->
  (k -> k -> Type -> Type) ->
  ((k -> k -> Type -> Type) -> k -> k -> k -> k -> Type -> Type -> Type) ->
  k ->
  k ->
  Type ->
  Type
data IProg effs f g p q a where
  Value :: a -> IProg effs f g p p a
  Impure ::
    Op effs x ->
    IKleisliTupled (IProg effs f g) '(p, x) '(r, a) ->
    IProg effs f g p r a
  ImpureT ::
    f p q x ->
    -- IProg f g p' q' x ->
    IKleisliTupled (IProg effs f g) '(q, x) '(r, a) ->
    -- (x' -> IProg f g q r a) ->
    IProg effs f g p r a
  ScopeT ::
    g (IProg effs f g) p p' q' q x x' ->
    -- IProg f g p' q' x ->
    IKleisliTupled (IProg effs f g) '(q, x') '(r, a) ->
    -- (x' -> IProg f g q r a) ->
    IProg effs f g p r a

instance Functor (IProg effs f g p q) where
  fmap f (Value a) = Value $ f a
  fmap f (Impure op k) = Impure op (IKleisliTupled $ fmap f . runIKleisliTupled k)
  fmap f (ImpureT op k) = ImpureT op (IKleisliTupled $ fmap f . runIKleisliTupled k)
  fmap f (ScopeT op k) = ScopeT op (IKleisliTupled $ fmap f . runIKleisliTupled k)

instance IFunctor (IProg effs f g) where
  imap f (Value a) = Value $ f a
  imap f (Impure op k) = Impure op (IKleisliTupled $ imap f . runIKleisliTupled k)
  imap f (ImpureT op k) = ImpureT op (IKleisliTupled $ imap f . runIKleisliTupled k)
  imap f (ScopeT op k) = ScopeT op (IKleisliTupled $ imap f . runIKleisliTupled k)

instance IApplicative (IProg effs f g) where
  pure = Value
  (Value f) <*> k = fmap f k
  (Impure fop k') <*> k = Impure fop (IKleisliTupled $ (<*> k) . runIKleisliTupled k')
  (ImpureT fop k') <*> k = ImpureT fop (IKleisliTupled $ (<*> k) . runIKleisliTupled k')
  ScopeT fop k' <*> k = ScopeT fop (IKleisliTupled $ (<*> k) . runIKleisliTupled k')

instance IMonad (IProg effs f g) where
  return :: a -> IProg effs f g i i a
  return = Value

  (>>=) :: IProg effs f g i j a -> (a -> IProg effs f g j k b) -> IProg effs f g i k b
  (Value a) >>= f = f a
  (Impure o k) >>= f = Impure o $ (IKleisliTupled $ (>>= f) . runIKleisliTupled k)
  (ImpureT o k) >>= f = ImpureT o $ (IKleisliTupled $ (>>= f) . runIKleisliTupled k)
  (ScopeT g k) >>= f = ScopeT g (IKleisliTupled $ (>>= f) . runIKleisliTupled k)

type family Fst x where
  Fst '(a, b) = a

type family Snd x where
  Snd '(a, b) = b

{- | Wrapper type that can carry additional type state.

 >>> :t runIKleisliTupled (undefined :: IKleisliTupled m '(p, a) '(q, b))
 runIKleisliTupled (undefined :: IKleisliTupled m '(p, a) '(q, b))
   :: forall k1 k2 k3 (p :: k1) a (m :: k1 -> k2 -> k3 -> *) (q :: k2)
             (b :: k3).
      a -> m p q b

 >>> :t runIKleisliTupled (undefined :: IKleisliTupled (Sem f) '(p, a) '(q, b))
 runIKleisliTupled (undefined :: IKleisliTupled (Sem f) '(p, a) '(q, b)) :: forall k p a (f :: [k -> k -> * -> *]) q b. a -> Sem f p q b
-}
newtype IKleisliTupled m ia ob = IKleisliTupled
  { runIKleisliTupled :: Snd ia -> m (Fst ia) (Fst ob) (Snd ob)
  }

(|>) :: IMonad m => IKleisliTupled m i o -> IKleisliTupled m o o2 -> IKleisliTupled m i o2
g |> f = IKleisliTupled $ \i -> runIKleisliTupled g i >>= runIKleisliTupled f

emptyCont :: IMonad m => IKleisliTupled m '(p, x) '(p, x)
emptyCont = IKleisliTupled Utils.return

transformKleisli ::
  (m (Fst ia) (Fst ob1) (Snd ob1) -> m (Fst ia) (Fst ob2) (Snd ob2)) ->
  IKleisliTupled m ia ob1 ->
  IKleisliTupled m ia ob2
transformKleisli f k = IKleisliTupled $ f . runIKleisliTupled k

-- type Op :: forall k.
--   [k -> k -> Type -> Type] ->
--   [k] ->
--   [k] ->
--   Type ->
--   Type
-- data Op effs t1 t2 x where
--   OHere ::
--     forall x f1 effs sl1 sl2 sr1 sr2 .
--     f1 sl1 sl2 x ->
--     Op (f1 : effs) (sl1 ': sr1) (sl2 ': sr2) x
--   OThere ::
--     forall x eff effs sr1 sr2 sl1 sl2 .
--     Op effs sr1 sr2 x ->
--     Op (eff : effs) (sl1 ': sr1) (sl2 ': sr2) x
--   deriving (Typeable)

-- Less general instance, note the entries sl and sr in the type level list
type Op ::
  [Type -> Type] ->
  Type ->
  Type
data Op f x where
  OHere :: f x -> Op (f : effs) x
  OThere :: Op effs x -> Op (eff : effs) x

type IVoid ::
  forall k.
  (k -> k -> Type -> Type) ->
  k ->
  k ->
  k ->
  k ->
  Type ->
  Type ->
  Type
data IVoid m p p' q' q x x'

run :: IProg '[] IIdentity IVoid p q a -> a
run (Value a) = a
run (Impure _cmd _k) = error "Impossible"
run (ImpureT cmd k) = run $ runIKleisliTupled k (runIIdentity cmd)
run (ScopeT _ _) = error "Impossible"

-- ------------------------------------------------
-- Sem Monad and Simple Runners
-- ------------------------------------------------

data IIdentity p q a where
  IIdentity :: a -> IIdentity p q a

runIIdentity :: IIdentity p q a -> a
runIIdentity (IIdentity a) = a

data IIO a where
  RunIO :: IO a -> IIO a

runIO :: IProg '[IIO] IIdentity IVoid p q a -> IO a
runIO (Value a) = P.pure a
runIO (Impure (OHere (RunIO a)) k) = a P.>>= \x -> runIO $ runIKleisliTupled k x
runIO (Impure (OThere _) _k) = error "Impossible"
runIO (ImpureT cmd k) = runIO $ runIKleisliTupled k (runIIdentity cmd)
runIO (ScopeT _ _) = error "Impossible"

embedIO :: SMember IIO effs => IO a -> IProg effs f g p p a
embedIO io = Impure (inj $ RunIO io) emptyCont

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
  FindEff e (e ': eff) = 0
  FindEff e (e' ': eff) = 1 + FindEff e eff

type family Write ind p ps where
  Write _ _ '[] = TypeError (Text "This sucks")
  Write 0 p (x : xs) = p : xs
  Write n p (x : xs) = x : Write (n - 1) p xs

type family Assume ind ps where
  Assume _ '[] = TypeError (Text "This sucks")
  Assume 0 (x : xs) = x
  Assume n (x : xs) = Assume (n - 1) xs

-- inj :: KnownNat n =>
--   proxy n -> e p q a -> Op effs ps qs a
-- inj pval op = go (natVal pval)
--   where
--     -- go :: Integer -> Op (e : effs2) (p : ps2) (q : qs2) a
--     go 0 = unsafeCoerce OHere op
--     go n = unsafeCoerce OThere (go (n - 1))

class SMember f effs where
  inj :: f a -> Op effs a

instance {-# OVERLAPPING #-} SMember e (e ': effs) where
  -- inj ::
  --   e () () a ->
  --   Op (e ': effs) (() ': ps) (() ': ps) a
  inj :: f a -> Op (f : effs) a
  inj e = OHere e

instance {-# INCOHERENT #-} SMember e effs => SMember e (eff ': effs) where
  inj = OThere . inj

instance
  TypeError
    ( Text "Failed to resolve effect " :<>: ShowType e
        :$$: Text "Perhaps check the type of effectful computation and the sequence of handlers for concordance?"
    ) =>
  SMember e '[]
  where
  inj = error "The instance of SMember e p q '[] must never be selected"

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

{- | Find the index of an element in a type-level list.
 The element must exist
 This is essentially a compile-time computation.
 Using overlapping instances here is OK since this class is private to this
 module
 class FindElem e p q effs pres posts where
   inj' :: e p q a -> Op effs pres posts a
-}

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
