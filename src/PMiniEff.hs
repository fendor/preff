{-# LANGUAGE UndecidableInstances #-}
module PMiniEff where

import qualified Prelude as P
import Control.IxMonad as Ix
import Data.Kind (Type)
import GHC.TypeLits hiding (Nat)
import Prelude hiding (Monad (..), Applicative(..))
import Unsafe.Coerce

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
  fmap = Ix.imap

instance P.Applicative (IProg f g p p) where
  pure = Ix.pure

  f <*> x = f Ix.<*> x

instance P.Monad (IProg f g p p) where
  a >>= f = a Ix.>>= f

instance IFunctor (IProg f g) where
  imap f (Pure a) = Pure $ f a
  imap f (Impure op k) = Impure op (IKleisliTupled $ imap f . runIKleisliTupled k)
  imap f (Scope op k) = Scope op (IKleisliTupled $ imap f . runIKleisliTupled k)

instance IApplicative (IProg f g) where
  pure = Pure
  (Pure f) <*> k = P.fmap f k
  (Impure fop k') <*> k = Impure fop (IKleisliTupled $ (<*> k) . runIKleisliTupled k')
  Scope fop k' <*> k = Scope fop (IKleisliTupled $ (<*> k) . runIKleisliTupled k')

instance IMonad (IProg f g) where
  return :: a -> IProg f g i i a
  return = Pure

  (>>=) :: IProg f g i j a -> (a -> IProg f g j k b) -> IProg f g i k b
  (Pure a) >>= f = f a
  (Impure o k) >>= f = Impure o $ (IKleisliTupled $ (>>= f) . runIKleisliTupled k)
  (Scope g k) >>= f = Scope g (IKleisliTupled $ (>>= f) . runIKleisliTupled k)

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
emptyCont = IKleisliTupled Ix.return

transformKleisli ::
  (m (Fst ia) (Fst ob1) (Snd ob1) -> m (Fst ia) (Fst ob2) (Snd ob2))
  -> IKleisliTupled m ia ob1
  -> IKleisliTupled m ia ob2
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
runI (Impure (OHere cmd) k) = runI $ unsafeCoerce runIKleisliTupled k (runIdentity cmd)
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
runIO (Impure (OHere (RunIO a)) k) = a P.>>= \x ->runIO $ runIKleisliTupled k x
runIO (Impure (OThere _) _k) = error "Impossible"
runIO (Scope _ _) = error "Impossible"

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
