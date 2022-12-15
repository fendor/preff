{-# LANGUAGE QuantifiedConstraints #-}

module Simple.Examples where

import Fcf
import GHC.TypeLits
import Simple.Reader
import Simple.State
import Parameterised.Protocol
import MiniEff
import qualified Control.IxMonad as Ix

readerExample :: Member (Reader e) eff =>
  MiniEff eff g p p e
readerExample = Ix.do
  x <- ask
  Ix.return x

-- runStateProt ::
--   e ->
--   MiniEff (StateS e: effs) Protocol p q a ->
--   MiniEff effs Protocol p q (e, a)
-- runStateProt s (Value a) = Ix.return (s, a)
-- runStateProt s (Impure (OHere GetS) k) = runStateProt s (runIKleisliTupled k s)
-- runStateProt _s (Impure (OHere (PutS s')) k) = runStateProt s' (runIKleisliTupled k ())
-- runStateProt s (Impure (OThere cmd) k) = Impure cmd $ IKleisliTupled (runStateProt s . runIKleisliTupled k)
-- runStateProt s (ImpureP cmd k) = ImpureP cmd (IKleisliTupled $ runStateProt s . runIKleisliTupled k)
-- runStateProt s (ScopedP op k) = case op of
--   LoopCUnbounded m -> Ix.do
--     aop <- runS s m
--     ScopedP aop
--       (IKleisliTupled $ \(e, x) -> runStateProt e $ runIKleisliTupled k x)

--   _ -> undefined

-- runS :: e
--   -> MiniEff (StateS e: effs) Protocol p' q' x
--   -> MiniEff effs Protocol p' q'
--       (ScopedE Protocol (MiniEff effs Protocol) p p' q' q (e, x) (e, [x]))
-- runS e act = Ix.do
--   let m' = runStateProt e act
--   Ix.return $ LoopCUnbounded m'
  -- LoopSUnbounded m ->
  --   let
  --     n = nt (m <$ ctx)
  --   in LoopSUnbounded n
  -- Sel1 m ->
  --   let
  --     n = nt (m <$ ctx)
  --   in
  --     Sel1 n
  -- Sel2 m ->
  --   let
  --     n = nt (m <$ ctx)
  --   in
  --     Sel2 n

  -- Offer m1 m2 ->
  --   let
  --     n1 = nt (m1 <$ ctx)
  --     n2 = nt (m2 <$ ctx)
  --   in
  --     Offer n1 n2

