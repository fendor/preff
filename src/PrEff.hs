{-# LANGUAGE TypeFamilyDependencies #-}
{-# LANGUAGE UndecidableInstances #-}

module PrEff where

import Control.IxMonad as Ix
import Data.Kind (Constraint, Type)
import GHC.TypeLits hiding (Nat)
import Unsafe.Coerce (unsafeCoerce)
import Prelude hiding (Applicative (..), Monad (..))
import qualified Prelude as P

-- ------------------------------------------------
-- Main Effect monad
-- ------------------------------------------------

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
  OHere :: eff x -> Op (eff : f) x
  OThere :: Op f x -> Op (eff : f) x

type PrEff ::
  forall k.
  [Type -> Type] ->
  (k -> k -> Type -> Type) ->
  k ->
  k ->
  Type ->
  Type
data PrEff f s p q a where
  Value :: a -> PrEff f s p p a
  Impure ::
    Op f x ->
    IKleisli (PrEff f s) p r x a ->
    PrEff f s p r a
  ImpureP ::
    s p q x ->
    IKleisli (PrEff f s) q r x a ->
    PrEff f s p r a
  ScopedP ::
    ScopeE s (PrEff f s) p p' q' q x x' ->
    IKleisli (PrEff f s) q r  x' a ->
    PrEff f s p r a

instance Functor (PrEff f s p q) where
  fmap = Ix.imap

instance P.Applicative (PrEff f s p p) where
  pure = Ix.pure
  f <*> x = f Ix.<*> x

instance P.Monad (PrEff f s p p) where
  a >>= f = a Ix.>>= f

instance IFunctor (PrEff f s) where
  imap f (Value a)      = Value $ f a
  imap f (Impure op k)  = Impure  op (imap f . k)
  imap f (ImpureP op k) = ImpureP op (imap f . k)
  imap f (ScopedP op k) = ScopedP op (imap f . k)

instance IApplicative (PrEff f s) where
  pure = Value
  Value k      <*> f = imap k f
  Impure  op k <*> f = Impure  op ((<*> f) . k)
  ImpureP op k <*> f = ImpureP op ((<*> f) . k)
  ScopedP op k <*> f = ScopedP op ((<*> f) . k)

instance IMonad (PrEff f s) where
  return = pure

  Value a      >>= f = f a
  Impure  op k >>= f = Impure  op ((>>= f) . k)
  ImpureP op k >>= f = ImpureP op ((>>= f) . k)
  ScopedP op k >>= f = ScopedP op ((>>= f) . k)

type family Fst x where
  Fst '(a, b) = a

type family Snd x where
  Snd '(a, b) = b

{- | Wrapper type that can carry additional type state.

>>> :t runIKleisli (undefined :: IKleisliTupled m '(p, a) '(q, b))
runIKleisli (undefined :: IKleisliTupled m '(p, a) '(q, b))
  :: forall {k1} {k2} {k3} {p :: k1} {a} {m :: k1 -> k2 -> k3 -> *}
            {q :: k2} {b :: k3}.
     a -> m p q b

>>> :t runIKleisli (undefined :: IKleisliTupled (PrEff f s) '(p, a) '(q, b))
runIKleisli (undefined :: IKleisliTupled (PrEff f s) '(p, a) '(q, b))
  :: forall {k2} {p :: k2} {a} {f :: [* -> *]}
            {s :: k2 -> k2 -> * -> *} {q :: k2} {b}.
     a -> PrEff f s p q b
-}
-- newtype IKleisliTupled m ia ob = IKleisliTupled
--   { runIKleisli :: Snd ia -> m (Fst ia) (Fst ob) (Snd ob)
--   }

type IKleisli m i o a b = a -> m i o b

iKleisli :: (a -> m i o b) -> IKleisli m i o a b
iKleisli = id

runIKleisli :: IKleisli m i o a b -> (a -> m i o b)
runIKleisli = id

emptyCont :: (IMonad m) => IKleisli m p p x x
emptyCont = iKleisli Ix.pure

transformKleisli ::
  (m i o b1 -> m i o b2) ->
  IKleisli m i o a b1 ->
  IKleisli m i o a b2
transformKleisli f k = iKleisli $ f . runIKleisli k

-- ------------------------------------------------
-- Scoped Algebras
-- ------------------------------------------------

type ScopeE :: forall k. (k -> k -> Type -> Type) -> (k -> k -> Type -> Type) -> k -> k -> k -> k -> Type -> Type -> Type
data family ScopeE s

type HandlerS c m n = forall r u v. c (m u v r) -> n u v (c r)

-- TODO: this is trash
type ScopedEffect :: forall k. (k -> k -> Type -> Type) -> Constraint
class ScopedEffect f where
  mapS ::
    (Functor c) =>
    c () ->
    (HandlerS c m n) ->
    ScopeE f m p p' q' q x x' ->
    ScopeE f n p p' q' q (c x) (c x')

weave ::
  (ScopedEffect s, Functor c) =>
  c () ->
  HandlerS c m n ->
  ScopeE s m p p' q' q x x' ->
  ScopeE s n p p' q' q (c x) (c x')
weave = mapS

-- ------------------------------------------------
-- Utility functions
-- ------------------------------------------------

send :: (Member eff f) => eff a -> PrEff f s p p a
send f = Impure (inj f) emptyCont

sendP :: s p q a -> PrEff eff s p q a
sendP f = ImpureP f emptyCont

sendScoped :: ScopeE s (PrEff eff s) p p' q' q x' x -> PrEff eff s p q x
sendScoped g = ScopedP g emptyCont

-- ------------------------------------------------
-- Algebraic Handlers
-- ------------------------------------------------

fold :: (forall x. Op f x -> x) -> (a -> b) -> PrEff f IVoid p q a -> b
fold alg gen (Value a) = gen a
fold alg gen (Impure op k) = fold alg gen (runIKleisli k (alg op))
fold alg gen _ = undefined

foldP ::
  AlgP s ->
  AlgScoped s ->
  Alg (Op f) ->
  Gen a b ->
  PrEff f s p q a ->
  b
foldP algP algScoped alg gen (Value a) =
  gen a
foldP algP algScoped alg gen (Impure op k) =
  foldP algP algScoped alg gen (runIKleisli k (alg op))
foldP algP algScoped alg gen (ImpureP op k) =
  foldP algP algScoped alg gen (runIKleisli k (algP op))
foldP algP algScoped alg gen (ScopedP op k) =
  foldP algP algScoped alg gen (runIKleisli k (algScoped op))

handleEff :: Alg f -> Gen a b -> PrEff (f : eff) IVoid p q a -> PrEff eff IVoid p q b
handleEff alg gen (Value a) = pure $ gen a
handleEff alg gen (Impure (OHere op) k) = handleEff alg gen (runIKleisli k (alg op))
handleEff alg gen (Impure (OThere op) k) = Impure op (iKleisli $ \x -> handleEff alg gen $ runIKleisli k x)
handleEff alg gen (ImpureP op k) = error "Impossible"
handleEff alg gen (ScopedP op k) = error "Impossible"

type Alg f = forall x. f x -> x
type AlgP f = forall x p q. f p q x -> x
type AlgScoped s = forall x m p p' q' q x'. ScopeE s m p p' q' q x' x -> x
type Gen a b = a -> b

-- ------------------------------------------------
-- PrEff Monad and Simple Runners
-- ------------------------------------------------

run :: PrEff '[] IVoid p q a -> a
run = foldP algIVoid algScopedIVoid (\_ -> undefined) genIVoid

-- Natural transformation
type (~>) f g = forall x. f x -> g x

interpret :: (ScopedEffect f) => (forall u. eff ~> PrEff effs f u u) -> PrEff (eff ': effs) f p q ~> PrEff effs f p q
interpret handler = \case
  Value a -> Value a
  Impure (OHere op) k -> Ix.do
    x <- handler op
    interpret handler (runIKleisli k x)
  Impure (OThere op) k ->
    Impure op (iKleisli $ \x -> interpret handler (runIKleisli k x))
  ImpureP op k ->
    ImpureP op (iKleisli $ \x -> interpret handler (runIKleisli k x))
  ScopedP op k ->
    ScopedP
      (mapS emptyCtx (\((), m) -> Ix.imap ((),) $ interpret handler m) op)
      (iKleisli $ \(_, x) -> interpret handler (runIKleisli k x))
   where
    emptyCtx = ((), ())

reinterpret :: (ScopedEffect f) => (forall u. eff ~> PrEff (newEff : effs) f u u) -> PrEff (eff ': effs) f p q ~> PrEff (newEff : effs) f p q
reinterpret handler = \case
  Value a -> Value a
  Impure (OHere op) k -> Ix.do
    x <- handler op
    reinterpret handler (runIKleisli k x)
  Impure (OThere op) k ->
    Impure (weaken op) (iKleisli $ \x -> reinterpret handler (runIKleisli k x))
  ImpureP op k ->
    ImpureP op (iKleisli $ \x -> reinterpret handler (runIKleisli k x))
  ScopedP op k ->
    ScopedP
      (mapS emptyCtx (\((), m) -> Ix.imap ((),) $ reinterpret handler m) op)
      (iKleisli $ \(_, x) -> reinterpret handler (runIKleisli k x))
   where
    emptyCtx = ((), ())

reinterpret2 :: (ScopedEffect f) => (forall u. eff ~> PrEff (e1 : e2 : effs) f u u) -> PrEff (eff ': effs) f p q ~> PrEff (e1 : e2 : effs) f p q
reinterpret2 handler = \case
  Value a -> Value a
  Impure (OHere op) k -> Ix.do
    x <- handler op
    reinterpret2 handler (runIKleisli k x)
  Impure (OThere op) k ->
    Impure (weaken $ weaken op) (iKleisli $ \x -> reinterpret2 handler (runIKleisli k x))
  ImpureP op k ->
    ImpureP op (iKleisli $ \x -> reinterpret2 handler (runIKleisli k x))
  ScopedP op k ->
    ScopedP
      (mapS emptyCtx (\((), m) -> Ix.imap ((),) $ reinterpret2 handler m) op)
      (iKleisli $ \(_, x) -> reinterpret2 handler (runIKleisli k x))
   where
    emptyCtx = ((), ())

interpretStateful ::
  (ScopedEffect f) =>
  s ->
  (forall v x. s -> eff x -> PrEff effs f v v (s, x)) ->
  PrEff (eff : effs) f ps qs a ->
  PrEff effs f ps qs (s, a)
interpretStateful !s _hdl (Value a) = Ix.return (s, a)
interpretStateful !s handler (Impure (OHere op) k) = Ix.do
  (newS, x) <- handler s op
  interpretStateful newS handler (runIKleisli k x)
interpretStateful !s hdl (Impure (OThere cmd) k) = Impure cmd $ iKleisli (interpretStateful s hdl . runIKleisli k)
interpretStateful !s hdl (ImpureP cmd k) = ImpureP cmd (iKleisli $ interpretStateful s hdl . runIKleisli k)
interpretStateful !s hdl (ScopedP op k) =
  ScopedP
    ( weave
        (s, ())
        ( \(s', inner) -> Ix.do
            (x, newS) <- interpretStateful s' hdl inner
            pure (x, newS)
        )
        op
    )
    (iKleisli $ \(s', a) -> interpretStateful s' hdl $ runIKleisli k a)

type RunnerS f m =
  forall u v x. u -> m u v x -> PrEff f IVoid () () (x, v)

type Runner f m =
  forall u v x. m u v x -> PrEff f IVoid () () x

type BaseAlgS f s =
  forall p' q' x. p' -> s p' q' x -> PrEff f IVoid () () (q', x)

type BaseAlg f s =
  forall p' q' x. s p' q' x -> PrEff f IVoid () () x

type ScopedAlgS f s =
  forall m p p' q' q x' x a.
  (m ~ PrEff f s) =>
  (forall r . IKleisli m q r x a) ->
  RunnerS f m ->
  p ->
  ScopeE s m p p' q' q x' x ->
  PrEff f IVoid () () (a, q)

type ScopedAlgS' f s =
  forall m p p' q' q x' x a.
  (m ~ PrEff f s) =>
  RunnerS f m ->
  p ->
  ScopeE s m p p' q' q x' x ->
  PrEff f IVoid () () (a, q)

type ScopedAlg f s =
  forall m p p' q' q x' x a r.
  (m ~ PrEff f s) =>
  IKleisli m q r x a ->
  Runner f m ->
  ScopeE s m p p' q' q x' x ->
  PrEff f IVoid () () a

type ScopedAlg' f s =
  forall m p p' q' q x' x .
  (m ~ PrEff f s) =>
  Runner f m ->
  ScopeE s m p p' q' q x' x ->
  PrEff f IVoid () () x

interpretStatefulScoped ::
  forall p f s q a.
  BaseAlgS f s ->
  ScopedAlgS f s ->
  p ->
  PrEff f s p q a ->
  PrEff f IVoid () () (a, q)
interpretStatefulScoped alg salg p (Value x) = Ix.return (x, p)
interpretStatefulScoped alg salg p (Impure cmd k) =
  Impure cmd
    $ iKleisli
    $ \x -> interpretStatefulScoped alg salg p $ runIKleisli k x
interpretStatefulScoped alg salg p (ImpureP op k) = Ix.do
  (q, a) <- alg p op
  interpretStatefulScoped alg salg q (runIKleisli k a)
interpretStatefulScoped alg salg p (ScopedP op k) =
  salg (unsafeCoerce k) (interpretStatefulScoped alg salg) p (unsafeCoerce op)

interpretStatefulScopedH ::
  forall p f s q a.
  BaseAlgS f s ->
  ScopedAlgS' f s ->
  p ->
  PrEff f s p q a ->
  PrEff f IVoid () () (a, q)
interpretStatefulScopedH alg salg p (Value x) = Ix.return (x, p)
interpretStatefulScopedH alg salg p (Impure cmd k) =
  Impure cmd
    $ iKleisli
    $ \x -> interpretStatefulScopedH alg salg p $ runIKleisli k x
interpretStatefulScopedH alg salg p (ImpureP op k) = Ix.do
  (q, a) <- alg p op
  interpretStatefulScopedH alg salg q (runIKleisli k a)
interpretStatefulScopedH alg salg p (ScopedP op k) = Ix.do
  (r, newS) <- salg (interpretStatefulScopedH alg salg) p op
  interpretStatefulScopedH alg salg newS (runIKleisli k r)

interpretScoped ::
  forall p f s q a.
  BaseAlg f s ->
  ScopedAlg f s ->
  PrEff f s p q a ->
  PrEff f IVoid () () a
interpretScoped alg salg (Value x) = Ix.return x
interpretScoped alg salg (Impure cmd k) =
  Impure cmd
    $ iKleisli
    $ \x -> interpretScoped alg salg $ runIKleisli k x
interpretScoped alg salg (ImpureP op k) = Ix.do
  a <- alg op
  interpretScoped alg salg (runIKleisli k a)
interpretScoped alg salg (ScopedP op k) =
  salg k (interpretScoped alg salg) op

interpretScopedH ::
  forall p f s q a.
  BaseAlg f s ->
  ScopedAlg' f s ->
  PrEff f s p q a ->
  PrEff f IVoid () () a
interpretScopedH alg salg (Value x) = Ix.return x
interpretScopedH alg salg (Impure cmd k) =
  Impure cmd
    $ iKleisli
    $ \x -> interpretScopedH alg salg $ runIKleisli k x
interpretScopedH alg salg (ImpureP op k) = Ix.do
  a <- alg op
  interpretScopedH alg salg (runIKleisli k a)
interpretScopedH alg salg (ScopedP op k) = Ix.do
  r <- salg (interpretScopedH alg salg) op
  interpretScopedH alg salg $ runIKleisli k r


-- runStateDirect ::
--   p ->
--   PrEff eff StateP p q a ->
--   PrEff eff IVoid () () (a, q)
-- runStateDirect p (Value x) = Ix.return (x, p)
-- runStateDirect p (Impure cmd k) =
--   Impure cmd $
--     IKleisliTupled $ \x -> runStateDirect p $ runIKleisli k x
-- runStateDirect p (ImpureP GetP k) =
--   runStateDirect p (runIKleisli k p)
-- runStateDirect _ (ImpureP (PutP q) k) =
--   runStateDirect q (runIKleisli k ())
-- runStateDirect p (ScopedP (ModifyP f m) k) = Ix.do
--   (x, _q) <- runStateDirect (f p) m
--   runStateDirect p (runIKleisli k x)

{- | Inject whole @'Union' r@ into a weaker @'Union' (any ': r)@ that has one
more summand.

/O(1)/
-}
weaken :: Op xs a -> Op (x : xs) a
weaken op = OThere op

-- data IIdentity p q a where
--  IIdentity :: a -> IIdentity p q a
data IVoid p q a

algIVoid :: AlgP IVoid
algIVoid _ = error "Invalid"

algScopedIVoid :: AlgScoped IVoid
algScopedIVoid _ = error "Invalid"

genIVoid :: Gen a a
genIVoid x = x

instance ScopedEffect IVoid where
  mapS ::
    (Functor c) =>
    c () ->
    (forall r u v. c (m u v r) -> n u v (c r)) ->
    ScopeE IVoid m p p' q' q x x' ->
    ScopeE IVoid n p p' q' q (c x) (c x')
  mapS ctx nt s = absurdS s

absurdS :: ScopeE IVoid m p p' q' q x x' -> a
absurdS v = error "Absurd"

-- runIIdentity :: IIdentity p q a -> a
-- runIIdentity (IIdentity a) = a

data instance ScopeE IVoid m p p' q' q x' x

runIO :: PrEff '[Embed IO] IVoid p q a -> IO a
runIO (Value a) = P.pure a
runIO (Impure (OHere (Embed a)) k) = do
  x <- a
  runIO $ runIKleisli k x
runIO (Impure (OThere _) _k) = error "Impossible"
runIO (ImpureP _cmd _k) = error "Impossible"
runIO (ScopedP _ _) = error "Impossible"

runEmbed ::
  (ScopedEffect s, P.Monad m) =>
  (forall x u v. m x -> PrEff effs s u v x) ->
  PrEff (Embed m : effs) s p q a ->
  PrEff effs s p q (m a)
runEmbed handle (Value a) = P.pure $ P.pure a
runEmbed handle (Impure (OHere (Embed m)) k) = Ix.do
  x <- handle m
  runEmbed handle $ runIKleisli k x
runEmbed handle (Impure (OThere _) _k) = error "Impossible"
runEmbed handle (ImpureP _cmd _k) = error "Impossible" -- runIO $ runIKleisli k (runIIdentity cmd)
runEmbed handle (ScopedP _ _) = error "Impossible"

embedIO :: (Member (Embed IO) effs) => IO a -> PrEff effs f p p a
embedIO io = embed io

data Embed m a where
  Embed :: m a -> Embed m a

embed :: (Member (Embed m) f) => m a -> PrEff f s p p a
embed act = send (Embed act)

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

-- type Operation a = a -> a -> Type -> Type

-- type Scope a = a -> a -> a -> a -> Type -> Type -> Type

type Apply :: forall k a. k a -> a -> a
type family Apply a b

type Reverse :: forall k a. k a -> a -> a -> a
type family Reverse a b c

-- type Map :: forall k a. k a -> [a] -> [a]
-- type family Map f a where
--   Map f '[] = '[]
--   Map f (x ': xs) = Apply f x ': Map f xs

type MapReverse :: forall k a. k a -> [a] -> [a] -> [a]
type family MapReverse f a b where
  MapReverse f '[] _ = '[]
  MapReverse f (x ': xs) (y ': ys) = Reverse f x y ': MapReverse f xs ys

type Take :: [a] -> Nat -> [a]
type family Take xs n where
  Take _ Z = '[]
  Take (x ': xs) (S n) = x ': Take xs n

data AccessLevel = N | R | X

-- data Container = Contains AccessLevel
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

instance (TypeError Msg) => X ≤ N

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

class Member eff f where
  inj :: eff a -> Op f a

instance {-# OVERLAPPING #-} Member e (e ': effs) where
  inj :: f a -> Op (f : effs) a
  inj e = OHere e

instance {-# INCOHERENT #-} (Member e effs) => Member e (eff ': effs) where
  inj = OThere . inj

instance
  ( TypeError
      ( Text "Failed to resolve effect "
          :<>: ShowType e
          :$$: Text "Perhaps check the type of effectful computation and the sequence of handlers for concordance?"
      )
  ) =>
  Member e '[]
  where
  inj = error "The instance of Member e '[] must never be selected"

type family Members fs effs where
  Members (f ': fs) effs = (Member f effs, Members fs effs)
  Members '[] effs = ()

