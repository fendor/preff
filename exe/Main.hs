{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE RebindableSyntax #-}
module Main where

import qualified Arrays
import Prelude hiding (Monad(..))

main :: IO ()
main = do
    -- Arrays.example20
    Arrays.example6
    -- Arrays.example21