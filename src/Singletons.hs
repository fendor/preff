{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE UndecidableInstances #-}

module Singletons where

import Data.Bool.Singletons
import Data.List.Singletons
import Data.Singletons
import Data.Singletons.TH
import GHC.TypeLits
import Prelude.Singletons

$( singletons
    [d|
        setAt :: Natural -> a -> [a] -> [a]
        setAt n p (x : xs) = if n == 0 then p : xs else x : setAt (n - 1) p xs
        setAt _ _ [] = error "Invalid Index"
        |]
 )

x :: Sing xs -> Sing (SetAt 0 5 xs)
x y = sSetAt (sing @0) (sing @5) y

-- getOut :: Sing (SetAt n p xs) -> Sing p
-- getOut m = undefined
