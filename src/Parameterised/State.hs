{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneKindSignatures #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -Wno-missing-signatures #-}

module Parameterised.State where

import Data.Kind
import Utils
import Prelude hiding (Monad (..))

data StateF p q x where
  Alloc :: t -> StateF p (Append p X) (Token t (Length p))
  Get ::
    (R ≤ Lookup p n) =>
    Token t n ->
    StateF p p t
  Put ::
    (X ≤ Lookup p n) =>
    Token t n ->
    t ->
    StateF p p ()

data StateG p p' q' q x x' where
  Fork :: (AcceptableList p1 q1 p2) => StateG p1 p2 q2 q1 a (Future a)
  Finish :: StateG p p q p a a

type Token :: Type -> Nat -> Type
newtype Token t n = Token ()

data Future a = Future

put a b = Impure (Put a b) return

alloc a = Impure (Alloc a) return

get a = Impure (Get a) return

fork s = Scope Fork s return

finish s = Scope Finish s return