{-# LANGUAGE TypeFamilyDependencies #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE EmptyCase #-}

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
    ScopeE s (PrEff f s) p p' q' q x' x ->
    IKleisli (PrEff f s) q r  x a ->
    PrEff f s p r a

-- deriving instance P.Functor (PrEff f s p q)

-- instance P.Applicative (PrEff f s p p) where
--   pure = Ix.pure
--   f <*> x = f Ix.<*> x

-- instance P.Monad (PrEff f s p p) where
--   a >>= f = a Ix.>>= f

instance IFunctor (PrEff f s) where
  imap f (Value a)      = Value $ f a
  imap f (Impure op k)  = Impure  op (imap f . k)
  imap f (ImpureP op k) = ImpureP op (imap f . k)
  imap f (ScopedP op k) = ScopedP op (imap f . k)
  {-# INLINE imap #-}

instance IApplicative (PrEff f s) where
  pure = Value
  Value k      <*> f = imap k f
  Impure  op k <*> f = Impure  op ((<*> f) . k)
  ImpureP op k <*> f = ImpureP op ((<*> f) . k)
  ScopedP op k <*> f = ScopedP op ((<*> f) . k)
  {-# INLINE pure #-}
  {-# INLINE (<*>) #-}

instance IMonad (PrEff f s) where
  return = pure

  Value a      >>= f = f a
  Impure  op k >>= f = Impure  op ((>>= f) . k)
  ImpureP op k >>= f = ImpureP op ((>>= f) . k)
  ScopedP op k >>= f = ScopedP op ((>>= f) . k)
  {-# INLINE (>>=) #-}

type family Fst x where
  Fst '(a, b) = a

type family Snd x where
  Snd '(a, b) = b

-- | Kleisli monad extended for parameterised monads.
--
-- @m i o a b = a -> m i o b@
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
-- Open union
-- ------------------------------------------------

type Op ::
  [Type -> Type] ->
  Type ->
  Type
data Op f x where
  OHere :: eff x -> Op (eff : f) x
  OThere :: Op f x -> Op (eff : f) x

{- | Inject whole @'Union' r@ into a weaker @'Union' (any ': r)@ that has one
more summand.

/O(1)/
-}
weaken :: Op xs a -> Op (x : xs) a
weaken op = OThere op

-- ------------------------------------------------
-- Scoped Algebras
-- ------------------------------------------------

type ScopeE :: forall k. (k -> k -> Type -> Type) -> (k -> k -> Type -> Type) -> k -> k -> k -> k -> Type -> Type -> Type
data family ScopeE s

type ScopedEffect :: forall k. (k -> k -> Type -> Type) -> Constraint
class ScopedEffect s where
  weave ::
    (Functor ctx, IFunctor n, IFunctor m) =>
    ctx () ->
    (forall u v r. ctx (m u v r) -> n u v (ctx r)) ->
    ScopeE s m p p' q' q x x' ->
    ScopeE s n p p' q' q (ctx x) (ctx x')

-- ------------------------------------------------
-- Base Scoped Effects and instances
-- ------------------------------------------------

data IVoid p q a

algIVoid :: AlgP IVoid
algIVoid = \case

algScopedIVoid :: AlgScoped IVoid
algScopedIVoid = \case

genIVoid :: Gen a a
genIVoid x = x

instance ScopedEffect IVoid where
  weave _ctx _nt s = absurdS s

absurdS :: ScopeE IVoid m p p' q' q x x' -> a
absurdS = \case

data instance ScopeE IVoid m p p' q' q x' x

-- ------------------------------------------------
-- Member type class
-- ------------------------------------------------

class Member eff f where
  inj :: eff a -> Op f a

instance {-# OVERLAPPING #-} Member e (e ': effs) where
  inj :: f a -> Op (f : effs) a
  inj e = OHere e

instance Member eff f => Member eff (e ': f) where
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

-- ------------------------------------------------
-- Utility functions
-- ------------------------------------------------

send ::
  Member eff f =>
  eff a ->
  PrEff f s p p a
send f =
  Impure (inj f) emptyCont

sendP ::
  s p q a ->
  PrEff f s p q a
sendP s =
  ImpureP s emptyCont

sendScoped ::
  ScopeE s (PrEff f s) p p' q' q x' x ->
  PrEff f s p q x
sendScoped scopedOp =
  ScopedP scopedOp emptyCont

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
-- Simple Runners and important effects
-- ------------------------------------------------

run :: PrEff '[] IVoid p q a -> a
run = foldP algIVoid algScopedIVoid (\_ -> undefined) genIVoid

runIO :: PrEff '[Embed IO] IVoid p q a -> IO a
runIO (Value a) = P.pure a
runIO (Impure (OHere (Embed a)) k) = do
  x <- a
  runIO $ runIKleisli k x
runIO (Impure (OThere _) _k) = error "Impossible"
runIO (ImpureP _cmd _k) = error "Impossible"
runIO (ScopedP _ _) = error "Impossible"

embedIO :: (Member (Embed IO) f) => IO a -> PrEff f s p p a
embedIO io = embed io

data Embed m a where
  Embed :: m a -> Embed m a

embed :: (Member (Embed m) f) => m a -> PrEff f s p p a
embed act = send (Embed act)

type family Concat s tail where
  Concat '[] t = t
  Concat (x ': xs) t = x : Concat xs t

-- ------------------------------------------------
-- Standard runners and type definitions
-- ------------------------------------------------

-- Natural transformation
type (~>) f g = forall x. f x -> g x

{-# INLINABLE interpret #-}
{-# INLINABLE reinterpret #-}
{-# INLINABLE reinterpret2 #-}
{-# INLINABLE interpretStateful #-}

interpret :: (ScopedEffect s) => (forall u. eff ~> PrEff f s u u) -> PrEff (eff ': f) s p q ~> PrEff f s p q
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
      (weave emptyCtx (\((), m) -> Ix.imap ((),) $ interpret handler m) op)
      (iKleisli $ \(_, x) -> interpret handler (runIKleisli k x))
   where
    emptyCtx = ((), ())

reinterpret :: (ScopedEffect s) => (forall u. eff ~> PrEff (newEff : f) s u u) -> PrEff (eff ': f) s p q ~> PrEff (newEff : f) s p q
reinterpret = reinterpretN weaken

reinterpret2 :: (ScopedEffect s) => (forall u. eff ~> PrEff (e1 : e2 : f) s u u) -> PrEff (eff ': f) s p q ~> PrEff (e1 : e2 : f) s p q
reinterpret2 = reinterpretN (weaken . weaken)

reinterpret3 :: (ScopedEffect s) => (forall u. eff ~> PrEff (e1 : e2 : e3: f) s u u) -> PrEff (eff ': f) s p q ~> PrEff (e1 : e2 : e3: f) s p q
reinterpret3 = reinterpretN (weaken . weaken . weaken)

reinterpretN :: (ScopedEffect s) => (forall x . Op f x -> Op fNew x) -> (forall u. eff ~> PrEff fNew s u u) -> PrEff (eff ': f) s p q ~> PrEff fNew s p q
reinterpretN weakenF handler = \case
  Value a -> Value a
  Impure (OHere op) k -> Ix.do
    x <- handler op
    reinterpretN weakenF handler (runIKleisli k x)
  Impure (OThere op) k ->
    Impure (weakenF op) (iKleisli $ \x -> reinterpretN weakenF handler (runIKleisli k x))
  ImpureP op k ->
    ImpureP op (iKleisli $ \x -> reinterpretN weakenF handler (runIKleisli k x))
  ScopedP op k ->
    ScopedP
      (weave emptyCtx (\((), m) -> Ix.imap ((),) $ reinterpretN weakenF handler m) op)
      (iKleisli $ \(_, x) -> reinterpretN weakenF handler (runIKleisli k x))
   where
    emptyCtx = ((), ())

interpretStateful ::
  ScopedEffect s =>
  e ->
  (forall v x. e -> eff x -> PrEff f s v v (e, x)) ->
  PrEff (eff : f) s ps qs a ->
  PrEff f s ps qs (e, a)
interpretStateful !s _hdl (Value a) = pure (s, a)
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
  forall m p p' q' q x' x.
  (m ~ PrEff f s) =>
  RunnerS f m ->
  p ->
  ScopeE s m p p' q' q x' x ->
  PrEff f IVoid () () (x, q)

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
interpretStatefulScoped alg salg p (Value x) = pure (x, p)
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
interpretStatefulScopedH alg salg p (Value x) = pure (x, p)
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
interpretScoped alg salg (Value x) = pure x
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
interpretScopedH alg salg (Value x) = pure x
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

-- ------------------------------------------------
-- Codensity experiments
-- ------------------------------------------------

type Eff f s p q x = ICodensity (PrEff f s) p q x

wrap :: PrEff f s p q x -> Eff f s p q x
wrap eff = ICodensity (eff >>=)

improve :: Eff f s p q x -> PrEff f s p q x
improve (ICodensity act) = act (\x -> pure x)

newtype ICodensity m j k a = ICodensity
  { runICodensity :: forall b i. (a -> m k i b) -> m j i b
  }

instance Ix.IFunctor (ICodensity m) where
  imap f (ICodensity run) = ICodensity $ \k ->
    run (\a -> k (f a))

instance Ix.IApplicative (ICodensity m) where
  pure :: a -> ICodensity m k k a
  pure a = ICodensity $ \k -> k a

  (<*>) :: ICodensity m i j (a -> b) -> ICodensity m j r a -> ICodensity m i r b
  f <*> g =
    ICodensity $ \bfr ->
      runICodensity f $ \ab -> runICodensity g $ \x ->  bfr (ab x)

instance Ix.IMonad (ICodensity m) where
  (>>=) ::
    ICodensity m j k a -> (a -> ICodensity m k r b) -> ICodensity m j r b
  m >>= k = ICodensity (\c ->
    runICodensity m $ \a -> runICodensity (k a) c)
