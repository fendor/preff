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

-- stateExample :: IProg (StateS Int) State'G () () String
-- stateExample = do
--     i <- getS @Int
--     putS (i+i)
--     Utils.return $ show i