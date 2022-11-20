module Simple.Reader where

import qualified Utils as I
import Utils
import GHC.TypeLits
import Data.Proxy

data Reader e p q a where
  Ask :: Reader e () () e

ask :: forall e effs g p r ind .
  (FindEff (Reader e) effs ~ ind, KnownNat ind) =>
  IProg effs g p r e
ask = Impure (inj (Proxy :: Proxy ind) Ask) emptyCont

runReader ::
  e ->
  IProg (Reader e: effs) IVoid (():p) (():q) a ->
  IProg effs IVoid p q a
runReader _e (Pure a) = I.return a
runReader e (Impure (OHere Ask) k) = runReader e (runIKleisliTupled k e)
runReader e (Impure (OThere cmd) k) = Impure cmd (IKleisliTupled $ runReader e . runIKleisliTupled k)
runReader _e (Scope _op _k) = error "This cannot happen"


