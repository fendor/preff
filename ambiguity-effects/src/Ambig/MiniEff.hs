module Ambig.PrEff where

import PrEff
import PrEff.Simple.State

manipState :: Member (State Int) effs => PrEff effs s p p ()
manipState = do
  i <- get
  put i
