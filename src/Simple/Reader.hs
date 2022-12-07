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

runReader ::
  e ->
  MiniEff (Reader e : effs) IVoid p q a ->
  MiniEff effs IVoid p q a
runReader _e (Value a) = I.return a
runReader e (Impure (OHere Ask) k) = runReader e (runIKleisliTupled k e)
runReader e (Impure (OThere cmd) k) = Impure cmd (IKleisliTupled $ runReader e . runIKleisliTupled k)
runReader e (ImpureT cmd k) = ImpureT cmd (IKleisliTupled $ runReader e . runIKleisliTupled k)
runReader _e (ScopedT _op _k) = error "This cannot happen"
