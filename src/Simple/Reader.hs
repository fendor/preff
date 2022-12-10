module Simple.Reader where

import MiniEff
import qualified Control.IxMonad as Ix

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
runReader _e (Value a) = Ix.return a
runReader e (Impure (OHere Ask) k) = runReader e (runIKleisliTupled k e)
runReader e (Impure (OThere cmd) k) = Impure cmd (IKleisliTupled $ runReader e . runIKleisliTupled k)
runReader e (ImpureP cmd k) = ImpureP cmd (IKleisliTupled $ runReader e . runIKleisliTupled k)
runReader e (ScopedP op k) =
  ScopedP
    (weave (e,()) (fmap (e,) . uncurry runReader) op)
    (IKleisliTupled $ \(_, x) -> runReader e $ runIKleisliTupled k x)

runReader' ::
  e ->
  MiniEff (Reader e : effs) IVoid p q a ->
  MiniEff effs IVoid p q a
runReader' e = handle (algReader e) genReader

algReader :: e -> Alg (Reader e)
algReader e = \case
  Ask -> e

genReader :: Gen a a
genReader x = x
