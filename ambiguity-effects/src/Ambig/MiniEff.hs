module Ambig.MiniEff where

import MiniEff
import MiniEff.Simple.State

manipState :: Member (State Int) effs => MiniEff effs s p p ()
manipState = do
  i <- get
  put i
