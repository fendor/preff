module PrEff.Codensity.Reader where

import PrEff

data Reader e a where
  Ask :: Reader e e

ask ::
  forall e effs f p.
  ( Member (Reader e) effs
  ) =>
  Eff effs f p p e
ask = wrap $ send Ask

runReader :: ScopedEffect s =>
  e ->
  PrEff (Reader e : effs) s p q a ->
  PrEff effs s p q a
runReader e = interpret $ \case
  Ask -> pure e

runReader' ::
  e ->
  PrEff (Reader e : effs) IVoid p q a ->
  PrEff effs IVoid p q a
runReader' e = handleEff (algReader e) genReader

algReader :: e -> Alg (Reader e)
algReader e = \case
  Ask -> e

genReader :: Gen a a
genReader x = x
