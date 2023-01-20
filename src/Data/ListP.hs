{-# LANGUAGE UndecidableInstances #-}
module Data.ListP where

import Data.Singletons
import GHC.Natural
import GHC.TypeLits

type family FindEff e effs :: Natural where
  FindEff e '[] = TypeError (Text "Not found")
  FindEff e (e ': eff) = 0
  FindEff e (e' ': eff) = 1 + FindEff e eff
