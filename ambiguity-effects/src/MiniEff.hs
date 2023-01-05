module MiniEff where

import MiniEff
import MiniEff.State

manipState :: Member (State Int) effs => MiniEff effs s p q ()
