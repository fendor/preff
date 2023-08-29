module PrEff.Parameterised.Reader where


import PrEff hiding (interpretStatefulScoped)
import qualified Control.IxMonad as Ix

data ReaderP p q a where
  Ask :: ReaderP p p p

data instance ScopeE ReaderP m p p' q' q x' x where
  Local :: (p -> p') -> m p' p' x -> ScopeE ReaderP m p p' p' p x x

-- runReaderP :: forall f p x .
--   p ->
--   PrEff f ReaderP p p x ->
--   PrEff f IVoid () () x
-- runReaderP p act =
--   fst <$> interpretStatefulScoped readerBaseAlg' p act

readerBaseAlg :: r -> ReaderP r v a -> a
readerBaseAlg r Ask = r

readerBaseAlg' :: r -> ReaderP r v a -> (v, a)
readerBaseAlg' r Ask = (r, r)

type Runner f p q a =
  p ->
  PrEff f ReaderP p q a ->
  PrEff f IVoid () () (a, q)

data ScopedAlg s = ScopedAlg
  { scopedAlg_base :: forall r v a . r -> s r v a -> (v, a)
  , scopedAlg_scoped ::
    forall r p' q' q a' a m f u v x.
      Runner f u v x ->
      r ->
      ScopeE s m r p' q' q a' a -> (a, q)
  }

-- readerScopedAlg' ::
--   (forall p' q' x. p' -> ReaderP p' q' x -> (q', x)) ->
--   ScopedAlg ReaderP
-- readerScopedAlg' baseAlg = ScopedAlg
--   { scopedAlg_base = baseAlg
--   , scopedAlg_scoped = \runner r -> \case
--       Local f m ->
--         runner (f r) m
--   }

type Interpreter i o f s p q a =
  i ->
  PrEff f s p q a ->
  PrEff f IVoid () () (a, o)

type ScopedAlgebra i o m f s p q a =
  Interpreter i o f s p q a ->
  (forall p' q' x' x. ScopeE s m p p' q' q x' x -> PrEff f IVoid () () (a, q))

-- scopedReaderAlgebra :: p -> ScopedAlgebra p q m f ReaderP p q a
-- scopedReaderAlgebra p interpreter = \case
--   Local f m -> do
--     interpreter (f p) m

interpretStatefulScoped ::
  (forall p' q' x. p' -> ReaderP p' q' x -> PrEff eff IVoid () () (q', x)) ->
  () ->
  p ->
  PrEff eff ReaderP p q a ->
  PrEff eff IVoid () () (a, q)
interpretStatefulScoped alg salg p (Value x) = Ix.return (x, p)
interpretStatefulScoped alg salg  p (Impure cmd k) =
  Impure cmd $
    IKleisliTupled $ \x -> interpretStatefulScoped alg salg  p $ runIKleisliTupled k x
interpretStatefulScoped alg salg  p (ImpureP op k) = do
  (q, a) <- alg p op
  interpretStatefulScoped alg salg  q (runIKleisliTupled k a)
interpretStatefulScoped alg salg  p (ScopedP (Local f m) k) = Ix.do
  (x, _q) <- interpretStatefulScoped alg salg (f p) m
  interpretStatefulScoped alg salg  p (runIKleisliTupled k x)

