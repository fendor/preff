{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE QuantifiedConstraints #-}

module PMiniEff where

import Control.IxMonad as Ix
import Data.Kind (Type)
import GHC.TypeLits hiding (Nat)
import Unsafe.Coerce
import Prelude hiding (Applicative (..), Monad (..))
import Prelude qualified as P
import Data.Proxy

data MiniEffP f p q a where
  Pure :: a -> MiniEffP f p p a
  Impure ::
    f p q x ->
    IKleisliTupled (MiniEffP f) '(q, x) '(r, a) ->
    -- (x -> MiniEffP f q r a)
    MiniEffP f p r a
  Scope ::
    ScopedE f (MiniEffP f) p p' q' q x x' ->
    -- MiniEffP f p' q' x ->
    IKleisliTupled (MiniEffP f) '(q, x') '(r, a) ->
    -- (x' -> MiniEffP f q r a) ->
    MiniEffP f p r a

instance Functor (MiniEffP f p q) where
  fmap = Ix.imap

instance P.Applicative (MiniEffP f p p) where
  pure = Ix.pure

  f <*> x = f Ix.<*> x

instance P.Monad (MiniEffP f p p) where
  a >>= f = a Ix.>>= f

instance IFunctor (MiniEffP f) where
  imap f (Pure a) = Pure $ f a
  imap f (Impure op k) = Impure op (IKleisliTupled $ imap f . runIKleisliTupled k)
  imap f (Scope op k) = Scope op (IKleisliTupled $ imap f . runIKleisliTupled k)

instance IApplicative (MiniEffP f) where
  pure = Pure
  (Pure f) <*> k = P.fmap f k
  (Impure fop k') <*> k = Impure fop (IKleisliTupled $ (<*> k) . runIKleisliTupled k')
  Scope fop k' <*> k = Scope fop (IKleisliTupled $ (<*> k) . runIKleisliTupled k')

instance IMonad (MiniEffP f) where
  return :: a -> MiniEffP f i i a
  return = Pure

  (>>=) :: MiniEffP f i j a -> (a -> MiniEffP f j k b) -> MiniEffP f i k b
  (Pure a) >>= f = f a
  (Impure o k) >>= f = Impure o $ (IKleisliTupled $ (>>= f) . runIKleisliTupled k)
  (Scope g k) >>= f = Scope g (IKleisliTupled $ (>>= f) . runIKleisliTupled k)

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
emptyCont = IKleisliTupled Ix.return

transformKleisli ::
  (m (Fst ia) (Fst ob1) (Snd ob1) -> m (Fst ia) (Fst ob2) (Snd ob2)) ->
  IKleisliTupled m ia ob1 ->
  IKleisliTupled m ia ob2
transformKleisli f k = IKleisliTupled $ f . runIKleisliTupled k

-- Less general instance, note the entries sl and sr in the type level list

type Op :: forall s k t .
  (s -> s -> Type -> Type, k) ->
  (s, t) ->
  (s, t) ->
  Type ->
  Type
data Op effs ps qs x where
  OHere ::
    f1 sl1 sl2 x ->
    Op '(f1, effs) '(sl1, sr) '(sl2, sr) x
  OThere ::
    Op effs sr1 sr2 x ->
    Op '(eff, effs) '(sl, sr1) '(sl, sr2) x

infixr 5 :+:
type (:+:) ::
  forall sl sr.
  (sl -> sl -> Type -> Type) ->
  (sr -> sr -> Type -> Type) ->
  (sl, sr) ->
  (sl, sr) ->
  Type ->
  Type
data (f1 :+: f2) p q x where
  PInl ::
    f1 p q x ->
    (f1 :+: f2) '(p, sr) '(q, sr) x
  PInr ::
    f2 sr1 sr2 x ->
    (f1 :+: f2) '(sl, sr1) '(sl, sr2) x

instance (Show (f p q x), Show (g ps qs x)) => Show ((f :+: g) '(p, ps) '(q, qs) x) where
  show (PInl f) = "PInl (" <> show f <> ")"
  show (PInr g) = "PInr (" <> show g <> ")"

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

type ScopeE :: forall k. (k -> k -> Type -> Type) -> (k -> k -> Type -> Type) -> k -> k -> k -> k -> Type -> Type -> Type
data family ScopeE f

type ScopedE f m p p' q' q x x' = ScopeE f m p p' q' q x x'

runI2 :: MiniEffP IIdentity () () a -> a
runI2 (Pure a) = a
runI2 (Impure (IIdentity a) k) = runI2 $ runIKleisliTupled k a
runI2 (Scope _ _) = error "Impossible"

-- ------------------------------------------------
-- Sem Monad and Simple Runners
-- ------------------------------------------------

data IIdentity p q a where
  IIdentity :: a -> IIdentity p p a

deriving instance Show a => Show (IIdentity p q a)

runIdentity :: IIdentity p q a -> a
runIdentity (IIdentity a) = a

type IIO :: forall k. k -> k -> Type -> Type
data IIO p q a where
  RunIO :: IO a -> IIO p p a

type family FindEff e effs :: Natural where
  FindEff e '[] = TypeError (Text "Not found")
  FindEff e (e ': eff) = 0
  FindEff e (f ': eff) = 1 + FindEff e eff

type family Write ind p ps where
  Write _ _ '[] = TypeError (Text "This sucks")
  Write 0 p (_ : xs) = p : xs
  Write n p (x : xs) = x : Write (n - 1) p xs

type family Assume ind ps where
  Assume _ '[] = TypeError (Text "This sucks")
  Assume 0 (x : xs) = x
  Assume n (x : xs) = Assume (n - 1) xs

inj ::
  KnownNat n =>
  proxy n ->
  e p q a ->
  Op effs ps qs a
inj pval op = go (natVal pval)
 where
  -- go :: Integer -> Op (e : effs2) (p : ps2) (q : qs2) a
  go 0 = unsafeCoerce OHere op
  go n = unsafeCoerce OThere (go (n - 1))

-- class PMember e p q effs pres posts where
--   injC :: e p q a -> effs pres posts a

-- instance {-# OVERLAPPING #-} PMember e p q (e :+: effs) '(p, ps) '(q, qs) where
--   injC ::
--     e p q a ->
--     (e :+: effs) '(p, ps) '(q, qs) a
--   injC e = unsafeCoerce PInl e

-- instance {-# INCOHERENT #-} PMember e p q effs ps qs => PMember e p q (eff :+: effs) '(s, ps) '(t, qs) where
--   injC = unsafeCoerce PInr . injC

-- instance
--   TypeError (Text "Failed to resolve effect " :<>: ShowType e :$$:
--              Text "Perhaps check the type of effectful computation and the sequence of handlers for concordance?"
--             )
--   => PMember e p q IIdentity '() '() where
--     injC = error "The instance of Member e p q '[] '[] '[] must never be selected"


data S a
data Z

data StateP p q a where
  PutP :: q -> StateP p q ()
  GetP :: StateP p p p

instance (Show q, Show p, Show x) => Show (StateP p q x) where
  show (PutP q) = "PutP " ++ show q
  show GetP = "GetP"

data State p q a where
  Put :: x -> State p x ()
  Get :: State p p p

get :: MiniEffP (State :+: r) '(p, ys) '(p, ys) p
get = Impure (PInl Get) (IKleisliTupled $ \x -> Ix.return x)

put :: q -> MiniEffP (State :+: r) '(p, ys) '(q, ys) ()
put q = Impure (PInl $ Put q) (IKleisliTupled $ \x -> Ix.return x)

data Reader e p q a where
  Ask :: Reader e (S z) z e

instance Show (Reader e p q a) where
  show Ask = "Ask"

data InputC p q a where
  Input :: InputC (x ': q) q x

askL2 :: MiniEffP (a :+: Reader e :+: r) '(p1, '(S x, p2)) '(p1, '(x, p2)) e
askL2 = Impure (PInr (PInl Ask)) (IKleisliTupled $ \x -> Ix.return x)

foo ::
  MiniEffP
    (State :+: Reader Int :+: IIdentity)
    '(Int, '(S (S Z), ()))
    '(String, '(Z, ()))
    Int
foo = Ix.do
  x <- askL2
  y <- askL2
  let r = x + y
  put (show r)
  Ix.return r

runStateAI ::
  p ->
  MiniEffP (State :+: eff) '(p, sr1) '(q, sr2) a ->
  MiniEffP eff sr1 sr2 (a, q)
runStateAI p (Pure x) = Ix.return (x, p)
runStateAI p (Impure (PInl Get) k) =
  runStateAI p (runIKleisliTupled k p)
runStateAI _ (Impure (PInl (Put q)) k) =
  runStateAI q (runIKleisliTupled k ())
runStateAI p (Impure (PInr op) k) =
  Impure op $ IKleisliTupled $ \x -> runStateAI p (runIKleisliTupled k x)
runStateAI _p (Scope _ _) = error "GHC is not exhaustive"

runReaderL ::
  e ->
  MiniEffP (Reader e :+: eff) '(p, sr1) '(Z, sr2) a ->
  MiniEffP eff sr1 sr2 a
runReaderL _ (Pure x) = Ix.return x
runReaderL p (Impure (PInl Ask) k) =
  runReaderL p (runIKleisliTupled k p)
runReaderL p (Impure (PInr op) k) =
  Impure op $ IKleisliTupled $ \x -> runReaderL p (runIKleisliTupled k x)
runReaderL _p (Scope _ _) = error "GHC is not exhaustive"

data family HList (l::[Type])

data instance HList '[] = HNil
data instance HList (x ': xs) = x `HCons` HList xs

runInputC ::
  HList p ->
  MiniEffP (InputC :+: eff) '(p, sr1) '( '[], sr2) a ->
  MiniEffP eff sr1 sr2 a
runInputC l = \case
  Pure x -> Ix.return x
  Impure (PInl Input) k -> case l of
    HCons p r ->
      runInputC r (runIKleisliTupled k p)
  Impure (PInr op) k ->
    Impure op $ IKleisliTupled $ \x -> runInputC l (runIKleisliTupled k x)
  _ -> error "Don't care for now"
