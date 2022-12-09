module Simple.Reader where

import Utils
import qualified Utils as I

data Reader e a where
  Ask :: Reader e e

ask ::
  forall e effs f p.
  ( Member (Reader e) effs
  ) =>
  MiniEff effs f p p e
ask = send Ask

runReader :: ScopedEffect s =>
  e ->
  MiniEff (Reader e : effs) s p q a ->
  MiniEff effs s p q a
runReader _e (Value a) = I.return a
runReader e (Impure (OHere Ask) k) = runReader e (runIKleisliTupled k e)
runReader e (Impure (OThere cmd) k) = Impure cmd (IKleisliTupled $ runReader e . runIKleisliTupled k)
runReader e (ImpureT cmd k) = ImpureT cmd (IKleisliTupled $ runReader e . runIKleisliTupled k)
runReader e (ScopedT op k) =
  ScopedT
    (weave (e,()) (fmap (e,) . uncurry runReader) op)
    (IKleisliTupled $ \(_, x) -> runReader e $ runIKleisliTupled k x)

runReader' ::
  e ->
  MiniEff (Reader e : effs) IVoid p q a ->
  MiniEff effs IVoid p q a
runReader' e = handle (\case
  Ask -> e
  )
  (\x -> x)

algReader :: e -> Alg (Reader e)
algReader e = \case
  Ask -> e

genReader :: Gen a a
genReader x = x
