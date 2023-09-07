module PrEff.Parameterised.Reader where


import PrEff
import qualified Control.IxMonad as Ix
import PrEff.Simple.Writer

data ReaderP p q a where
  Ask :: ReaderP p p p

data instance ScopeE ReaderP m p p' q' q x' x where
  Local :: (p -> p') -> m p' p' x -> ScopeE ReaderP m p p' p' p x x

ask :: PrEff eff ReaderP a a a
ask = sendP Ask

local :: (q -> q') -> PrEff eff ReaderP q' q' x -> PrEff eff ReaderP q q x
local f m = sendScoped (Local f m)

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

readerBaseAlgM' :: Monad m => r -> ReaderP r v a -> m (v, a)
readerBaseAlgM' r Ask = pure (r, r)

type Interpreter i o f s p q a =
  i ->
  PrEff f s p q a ->
  PrEff f IVoid () () (a, o)

type ScopedAlgebra i o m f s p q a =
  Interpreter i o f s p q a ->
  (forall p' q' x' x. ScopeE s m p p' q' q x' x -> PrEff f IVoid () () (a, q))

runReaderP :: p -> PrEff f ReaderP p q a -> PrEff f IVoid () () (a, q)
runReaderP = interpretStatefulScoped readerBaseAlgM' scopedAlg

scopedAlg :: ScopedAlgS f ReaderP
  -- (m ~ PrEff f ReaderP) =>
  -- (forall r . IKleisliTupled m '(q, x) '(r, a)) ->
  -- Runner f m ->
  -- p ->
  -- ScopedE ReaderP m p p' q' q x' x ->
  -- PrEff f IVoid () () (a, q)
scopedAlg k runner s = \case
  Local f m -> Ix.do
    (x, _q) <- runner (f s) m
    runner s (runIKleisli k x)

example :: Member (Writer [String]) f => PrEff f ReaderP Int Int String
example = Ix.do
  tell ["Start"]
  i <- ask
  tell ["Value: " ++ show i]
  local (show . (*2)) $ Ix.do
    s <- ask
    tell ["Now it is: " <> s]
  pure $ show i

runExample = run $ runWriter @[String] $ runReaderP (5 :: Int) example

-- >>> runExample
-- (["Start","Value: 5","Now it is: 10"],("5",5))
