{-# LANGUAGE UndecidableInstances #-}
module PrEff.Parameterised.NonDet where

import PrEff
import qualified Control.IxMonad as Ix
import Data.Proxy

data Z
data S z

deriving instance Show Z
deriving instance Show z => Show (S z)

class NatVal v where
  natVal :: proxy v -> Integer

instance NatVal Z where
  natVal _ = 0

instance NatVal z => NatVal (S z) where
  natVal _ = 1 + natVal (Proxy :: Proxy z)

type family Add x y where
  Add Z z = z
  Add (S x) z = Add x (S z)

data NonDet p q a where
  Empty :: NonDet p p a


data instance ScopeE NonDet m p p' q' q x' x where
  Choose :: m p v x -> m p h x -> ScopeE NonDet m p p p p x x


