{-# LANGUAGE QuantifiedConstraints #-}

module Simple.Examples where

import Fcf
import GHC.TypeLits
import Simple.Reader
import Simple.State
import Utils
import qualified Utils as Ix

readerExample :: Member (Reader e) eff =>
  MiniEff eff g p p e
readerExample = Ix.do
  x <- ask
  Ix.return x
