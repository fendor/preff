module PrEff.Parameterised.Reader where


import PrEff hiding (interpretStatefulScoped)
import qualified Control.IxMonad as Ix

data ReaderP p q a where
  Ask :: ReaderP p p p

data instance ScopeE ReaderP m p p' q' q x' x where
  Local :: (p -> p') -> m p' p' x -> ScopeE ReaderP m p p' p' p x x

runReaderP :: forall f p x .
  p ->
  PrEff f ReaderP p p x ->
  PrEff f IVoid () () x
runReaderP p act =
  fst <$> interpretStatefulScoped readerBaseAlg' p act

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



interpretStatefulScoped ::
  (forall p' q' x. p' -> ReaderP p' q' x -> (q', x)) ->
  p ->
  PrEff eff ReaderP p q a ->
  PrEff eff IVoid () () (a, q)
interpretStatefulScoped alg p (Value x) = Ix.return (x, p)
interpretStatefulScoped alg p (Impure cmd k) =
  Impure cmd $
    IKleisliTupled $ \x -> interpretStatefulScoped alg p $ runIKleisliTupled k x
interpretStatefulScoped alg p (ImpureP op k) = do
  let (q, a) = alg p op
  interpretStatefulScoped alg q (runIKleisliTupled k a)
interpretStatefulScoped alg p (ScopedP (Local f m) k) = Ix.do
  (x, _q) <- interpretStatefulScoped alg (f p) m
  interpretStatefulScoped alg p (runIKleisliTupled k x)

