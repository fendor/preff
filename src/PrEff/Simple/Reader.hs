module PrEff.Simple.Reader where

import PrEff
import qualified Control.IxMonad as Ix

data Reader e a where
  Ask :: Reader e e

ask ::
  forall e effs f p.
  ( Member (Reader e) effs
  ) =>
  PrEff effs f p p e
ask = send Ask

runReader :: ScopedEffect s =>
  e ->
  PrEff (Reader e : effs) s p q a ->
  PrEff effs s p q a
runReader _e (Value a) = Ix.return a
runReader e (Impure (OHere Ask) k) = runReader e (runIKleisliTupled k e)
runReader e (Impure (OThere cmd) k) = Impure cmd $ hdl (runReader e) k
runReader e (ImpureP cmd k) = ImpureP cmd $ hdl (runReader e) k
runReader e (ScopedP op k) =
  ScopedP
    (weave (e,()) (fmap (e,) . uncurry runReader) op)
    (IKleisliTupled $ \(_, x) -> runReader e $ runIKleisliTupled k x)

runReaderI :: ScopedEffect s =>
  e ->
  PrEff (Reader e : effs) s p q a ->
  PrEff effs s p q a
runReaderI e = interpret $ \case
  Ask -> pure e

runReader' ::
  e ->
  PrEff (Reader e : effs) IVoid p q a ->
  PrEff effs IVoid p q a
runReader' e = handle (algReader e) genReader

algReader :: e -> Alg (Reader e)
algReader e = \case
  Ask -> e

genReader :: Gen a a
genReader x = x
