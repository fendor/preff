module Simple.Reader where

import Utils
import qualified Utils as I

data Reader e a where
  Ask :: Reader e e

ask ::
  forall e effs f g p.
  ( SMember (Reader e) effs
  ) =>
  MiniEff effs f g p p e
ask = Impure (inj Ask) emptyCont

runReader ::
  e ->
  MiniEff (Reader e : effs) IIdentity IVoid p q a ->
  MiniEff effs IIdentity IVoid p q a
runReader _e (Value a) = I.return a
runReader e (Impure (OHere Ask) k) = runReader e (runIKleisliTupled k e)
runReader e (Impure (OThere cmd) k) = Impure cmd (IKleisliTupled $ runReader e . runIKleisliTupled k)
runReader e (ImpureT cmd k) = ImpureT cmd (IKleisliTupled $ runReader e . runIKleisliTupled k)
runReader _e (ScopeT _op _k) = error "This cannot happen"
