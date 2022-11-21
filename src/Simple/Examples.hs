{-# LANGUAGE QuantifiedConstraints #-}
module Simple.Examples where

import qualified Utils as I
import Utils
import Simple.Reader
import Simple.State
import GHC.TypeLits
import Fcf

type SMember e effs i = (FindEff e effs ~ i, KnownNat i)


-- foo ::
--   ( SMember (Reader Int) effs reader
--   , SMember (StateS String) effs state
--   ) =>
--   IProg effs (StateG String) ps ps String
foo ::
  ( FindEff (Reader Int) effs ~ reader, KnownNat reader
  , FindEff (StateS String) effs ~ state, KnownNat state
  , ps ~ ((): sr)
  ) =>
  IProg effs (StateG String) ps ps String
foo = I.do
  n <- ask @Int
  s <- getS @String
  putS (s ++ ": " ++ show n)
  m <- modifyG (\_ -> "") $ I.do
    e <- getS @String
    n' <- ask @Int
    putS ("Found num: " ++ show n' ++ ", localed: \"" ++ e ++ "\"")
    getS

  s' <- getS @String
  I.return $ unlines
    [ "First get: " ++ s
    , "After Modify: " ++ m
    , "Last: " ++ s'
    ]

runFoo :: (String, String)
runFoo = run $ runReader (5 :: Int) $ runStateG "Example" foo
