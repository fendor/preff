{-# LANGUAGE QualifiedDo #-}

module Parameterised.Protocol where

import Data.Kind
import MiniEff hiding (send)
import qualified Control.IxMonad as Ix
import Simple.State

-- type End :: Type
data End
data S a
data R a
data C a b
data O a b
data SL n a
data CL n a
data SLU a
data CLU a

type Protocol ::
  forall k.
  [k] ->
  [k] ->
  Type ->
  Type
data Protocol p q r where
  Send :: a -> Protocol (S a : p) p ()
  Recv :: Protocol (R a : p) p a

data instance ScopeE Protocol m p p' q' q x x' where
  LoopSUnbounded ::
    m a '[End] (Maybe x) ->
    ScopeE Protocol m (SLU a : c) a '[End] c (Maybe x) [x]
  LoopCUnbounded ::
    m a '[End] x ->
    ScopeE Protocol m (CLU a : r) a '[End] r x [x]
  Sel1 ::
    m a '[End] x ->
    ScopeE Protocol m (C a b : c) a '[End] c x x
  Sel2 ::
    m b '[End] x ->
    ScopeE Protocol m (C a b : c) b '[End] c x x
  Offer ::
    m a '[End] x ->
    m b '[End] x ->
    ScopeE Protocol m (O a b : c) '[O a b] '[End] c x x

-- myweave :: Functor ctx =>
--   ctx () ->
--   -- natural transformation
--   (forall r u v. ctx (m u v r) -> n u v (ctx r)) ->
--   ScopedP Protocol m p p' q' q x x' ->
--   ScopedP Protocol n p p' q' q (ctx x) (ctx x')
-- myweave ctx nt = \case
--   LoopCUnbounded m ->
--     let
--       n = nt (m <$ ctx)
--     in LoopCUnbounded n
--   LoopSUnbounded m ->
--     let
--       n = nt (m <$ ctx)
--     in do
--       unsafeCoerce LoopSUnbounded n
--   Sel1 m ->
--     let
--       n = nt (m <$ ctx)
--     in
--       Sel1 n
--   Sel2 m ->
--     let
--       n = nt (m <$ ctx)
--     in
--       Sel2 n

--   Offer m1 m2 ->
--     let
--       n1 = nt (m1 <$ ctx)
--       n2 = nt (m2 <$ ctx)
--     in
--       Offer n1 n2

type family Dual proc where
  Dual (R a : p) = S a : Dual p
  Dual (S a : p) = R a : Dual p
  Dual (O a b : c) = C (Dual a) (Dual b) : Dual c
  Dual (C a b : c) = O (Dual a) (Dual b) : Dual c
  Dual (CLU a : c) = SLU (Dual a) : Dual c
  Dual (SLU a : c) = CLU (Dual a) : Dual c
  Dual '[End] = '[End]

send ::
  forall a effs p.
  a ->
  MiniEff effs Protocol (S a : p) p ()
send a = sendP (Send a)

recv ::
  forall a p effs.
  MiniEff effs Protocol (R a : p) p a
recv = sendP Recv

sel1 ::
  MiniEff effs Protocol p' '[End] a ->
  MiniEff effs Protocol (C p' b : r) r a
sel1 act = sendScoped (Sel1 act)

sel2 ::
  MiniEff effs Protocol p' '[End] a1 ->
  MiniEff effs Protocol (C a2 p' : r) r a1
sel2 act = sendScoped (Sel2 act)

offer ::
  MiniEff effs Protocol a1 '[End] a2 ->
  MiniEff effs Protocol b '[End] a2 ->
  MiniEff effs Protocol (O a1 b : r) r a2
offer s1 s2 = sendScoped (Offer s1 s2)

loopS ::
  MiniEff effs Protocol a '[End] (Maybe x) ->
  MiniEff effs Protocol (SLU a: r) r [x]
loopS act = sendScoped (LoopSUnbounded act)

loopC ::
  MiniEff effs Protocol a '[End] x ->
  MiniEff effs Protocol (CLU a: r) r [x]
loopC act = sendScoped (LoopCUnbounded act)

simpleServer :: MiniEff effs Protocol (S Int : R String : k) k String
simpleServer = Ix.do
  send @Int 5
  s <- recv @String
  Ix.return s

simpleClient :: MiniEff effs Protocol (R Int : S String : k) k ()
simpleClient = Ix.do
  n <- recv @Int
  send (show $ n * 25)

serverLoop :: Member (StateS Int) effs => MiniEff effs Protocol (SLU '[S Int, R Int, End] : r) r [Int]
serverLoop = Ix.do
  loopS $ Ix.do
    x <- getS
    send x
    n :: Int <- recv
    putS n
    if n < 10
      then
        Ix.return Nothing
      else
        Ix.return $ Just n

clientLoop :: MiniEff effs Protocol (CLU '[R Int, S Int, End] : r) r [()]
clientLoop = Ix.do
  loopC $ Ix.do
    n :: Int <- recv
    send (n - 1)
    Ix.return ()

choice ::
  MiniEff
    effs
    Protocol
    (S Int : C '[R Int, End] b : k2)
    k2
    Int
choice = Ix.do
  send @Int 5
  sel1 $ Ix.do
    n <- recv @Int
    Ix.return n

andOffer ::
  MiniEff
    effs
    Protocol
    (R Int : O '[S Int, End] '[S Int, End] : k)
    k
    ()
andOffer = Ix.do
  n <- recv @Int
  offer
    ( Ix.do
        send @Int n
    )
    ( Ix.do
        send @Int n
    )
  Ix.return ()

choice2 ::
  MiniEff
    effs
    Protocol
    (R Int : C '[R String, End] '[S String, R String, End] : k)
    k
    String
choice2 = Ix.do
  n <- recv @Int
  ifThenElse
    (n < 0)
    ( Ix.do
        sel1 $ Ix.do
          x <- recv @String
          Ix.return x
    )
    ( Ix.do
        sel2 $ Ix.do
          send @String "Test"
          x <- recv @String
          Ix.return x
    )

connect ::
  (Dual p1 ~ p2, Dual p2 ~ p1) =>
  MiniEff '[] Protocol p1 '[End] a ->
  MiniEff '[] Protocol p2 '[End] b ->
  MiniEff '[] IVoid () () (a, b)
connect (Value x) (Value y) = Ix.return (x, y)
connect (ImpureP (Recv) k1) (ImpureP ((Send a)) k2) = connect (runIKleisliTupled k1 a) (runIKleisliTupled k2 ())
connect (ImpureP ((Send a)) k1) (ImpureP (Recv) k2) = connect (runIKleisliTupled k1 ()) (runIKleisliTupled k2 a)
connect (ScopedP (Sel1 act1) k1) (ScopedP (Offer act2 _) k2) = Ix.do
  (a, b) <- connect act1 act2
  connect (runIKleisliTupled k1 a) (runIKleisliTupled k2 b)
connect (ScopedP (Sel2 act1) k1) (ScopedP (Offer _ act2) k2) = Ix.do
  (a, b) <- connect act1 act2
  connect (runIKleisliTupled k1 a) (runIKleisliTupled k2 b)
connect (ScopedP (Offer act1 _) k1) (ScopedP (Sel1 act2) k2) = Ix.do
  (a, b) <- connect act1 act2
  connect (runIKleisliTupled k1 a) (runIKleisliTupled k2 b)
connect (ScopedP (Offer _ act1) k1) (ScopedP (Sel2 act2) k2) = Ix.do
  (a, b) <- connect act1 act2
  connect (runIKleisliTupled k1 a) (runIKleisliTupled k2 b)
connect (ScopedP (LoopSUnbounded act1) k1) (ScopedP (LoopCUnbounded act2) k2) = Ix.do
  (a, b) <- go ([], [])
  connect (runIKleisliTupled k1 a) (runIKleisliTupled k2 b)
  where
    go (r1, r2) = Ix.do
      (a, b) <- connect act1 act2
      case a of
        Nothing -> Ix.return (r1, b:r2)
        Just a' -> go (a': r1, b:r2)
-- TODO: case missing for the other loop case


connect _ _ = error "Procol.connect: internal tree error"


connect' ::
  (Dual p1 ~ p2, Dual p2 ~ p1) =>
  MiniEff effs Protocol p1 '[End] a ->
  MiniEff effs Protocol p2 '[End] b ->
  MiniEff effs IVoid () () (a, b)
connect' (Value x) (Value y) = Ix.return (x, y)
connect' (ImpureP (Recv) k1) (ImpureP ((Send a)) k2) = connect' (runIKleisliTupled k1 a) (runIKleisliTupled k2 ())
connect' (ImpureP ((Send a)) k1) (ImpureP (Recv) k2) = connect' (runIKleisliTupled k1 ()) (runIKleisliTupled k2 a)
connect' (ScopedP (Sel1 act1) k1) (ScopedP (Offer act2 _) k2) = Ix.do
  (a, b) <- connect' act1 act2
  connect' (runIKleisliTupled k1 a) (runIKleisliTupled k2 b)
connect' (ScopedP (Sel2 act1) k1) (ScopedP (Offer _ act2) k2) = Ix.do
  (a, b) <- connect' act1 act2
  connect' (runIKleisliTupled k1 a) (runIKleisliTupled k2 b)
connect' (ScopedP (Offer act1 _) k1) (ScopedP (Sel1 act2) k2) = Ix.do
  (a, b) <- connect' act1 act2
  connect' (runIKleisliTupled k1 a) (runIKleisliTupled k2 b)
connect' (ScopedP (Offer _ act1) k1) (ScopedP (Sel2 act2) k2) = Ix.do
  (a, b) <- connect' act1 act2
  connect' (runIKleisliTupled k1 a) (runIKleisliTupled k2 b)
connect' (ScopedP (LoopSUnbounded act1) k1) (ScopedP (LoopCUnbounded act2) k2) = Ix.do
  (a, b) <- go ([], [])
  connect' (runIKleisliTupled k1 a) (runIKleisliTupled k2 b)
  where
    go (r1, r2) = Ix.do
      (a, b) <- connect' act1 act2
      case a of
        Nothing -> Ix.return (r1, b:r2)
        Just a' -> go (a': r1, b:r2)
connect' (ScopedP (LoopCUnbounded act1) k1) (ScopedP (LoopSUnbounded act2) k2) = Ix.do
  (a, b) <- go ([], [])
  connect' (runIKleisliTupled k1 a) (runIKleisliTupled k2 b)
  where
    go (r1, r2) = Ix.do
      (a, b) <- connect' act1 act2
      case b of
        Nothing -> Ix.return (a:r1, r2)
        Just b' -> go (a: r1, b':r2)

connect' (Impure cmd k1) k2 = Impure cmd $ IKleisliTupled $ \x -> connect' (runIKleisliTupled k1 x) k2
connect' k1 (Impure cmd k2) = Impure cmd $ IKleisliTupled $ \x -> connect' k1 (runIKleisliTupled  k2 x)
connect' _ _ = error "Procol.connect: internal tree error"
