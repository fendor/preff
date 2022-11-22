{-# LANGUAGE QualifiedDo #-}

module Parameterised.Protocol where

import Data.Kind
import Utils
import qualified Utils as Ix
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

type ProtocolG ::
  forall k.
  ([k] -> [k] -> Type -> Type) ->
  [k] ->
  [k] ->
  [k] ->
  [k] ->
  Type ->
  Type ->
  Type
data ProtocolG m p p' q' q x x' where
  LoopSUnbounded ::
    m a '[End] (Maybe x) ->
    ProtocolG m (SLU a : c) a '[End] c (Maybe x) [x]
  LoopCUnbounded ::
    m a '[End] x ->
    ProtocolG m (CLU a : c) a '[End] c x [x]
  Sel1 ::
    m a '[End] x ->
    ProtocolG m (C a b : c) a '[End] c x x
  Sel2 ::
    m b '[End] x ->
    ProtocolG m (C a b : c) b '[End] c x x
  Offer ::
    m a '[End] x ->
    m b '[End] x ->
    ProtocolG m (O a b : c) '[O a b] '[End] c x x

type family Dual proc where
  Dual (R a : p) = S a : Dual p
  Dual (S a : p) = R a : Dual p
  Dual (O a b : c) = C (Dual a) (Dual b) : Dual c
  Dual (C a b : c) = O (Dual a) (Dual b) : Dual c
  Dual (CLU a : c) = SLU (Dual a) : Dual c
  Dual (SLU a : c) = CLU (Dual a) : Dual c
  Dual '[End] = '[End]

send ::
  forall a effs g p.
  a ->
  IProg effs Protocol g (S a : p) p ()
send a = ImpureT ((Send a)) (IKleisliTupled Utils.return)

-- recv :: IProg (Protocol :+: IIdentity) ProtocolG '(a :? p, sr) '(p, sr) a
recv ::
  forall a p effs g.
  IProg effs Protocol g (R a : p) p a
recv = ImpureT (Recv) (IKleisliTupled Utils.return)

-- sel1 ::
--     IProg effs f ProtocolG '[a] '[End] a ->
--     IProg effs f ProtocolG (C a b : r) r a
sel1 ::
  IProg effs f ProtocolG p' '[End] a ->
  IProg effs f ProtocolG (C p' b : r) r a
sel1 act = ScopeT (Sel1 act) (IKleisliTupled Utils.return)

-- sel2 ::
--     IProg effs f ProtocolG b End a2 ->
--     IProg effs f ProtocolG (C a b) r a2
sel2 ::
  IProg effs f ProtocolG p' '[End] a1 ->
  IProg effs f ProtocolG (C a2 p' : r) r a1
sel2 act = ScopeT (Sel2 act) (IKleisliTupled Utils.return)

-- offer ::
--     IProg effs f ProtocolG a End a2 ->
--     IProg effs f ProtocolG b End a2 ->
--     IProg effs f ProtocolG (O a b : c) c a2
offer ::
  IProg effs f ProtocolG a1 '[End] a2 ->
  IProg effs f ProtocolG b '[End] a2 ->
  IProg effs f ProtocolG (O a1 b : r) r a2
offer s1 s2 = ScopeT (Offer s1 s2) emptyCont

loopS ::
  IProg effs f ProtocolG a '[End] (Maybe x) ->
  IProg effs f ProtocolG (SLU a: r) r [x]
loopS act = ScopeT (LoopSUnbounded act) emptyCont

loopC ::
  IProg effs f ProtocolG a '[End] x ->
  IProg effs f ProtocolG (CLU a: r) r [x]
loopC act = ScopeT (LoopCUnbounded act) emptyCont

simpleServer :: IProg effs Protocol g (S Int : R String : k) k String
simpleServer = Ix.do
  send @Int 5
  s <- recv @String
  Ix.return s

simpleClient :: IProg effs Protocol g (R Int : S String : k) k ()
simpleClient = Ix.do
  n <- recv @Int
  send (show $ n * 25)


serverLoop :: SMember (StateS Int) effs => IProg effs Protocol ProtocolG (SLU '[S Int, R Int, End] : r) r [Int]
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

clientLoop :: IProg effs Protocol ProtocolG (CLU '[R Int, S Int, End] : r) r [()]
clientLoop = Ix.do
  loopC $ Ix.do
    n :: Int <- recv
    send (n - 1)
    Ix.return ()

choice ::
  IProg
    effs
    Protocol
    ProtocolG
    (S Int : C '[R Int, End] b : k2)
    k2
    Int
choice = Ix.do
  send @Int 5
  sel1 $ Ix.do
    n <- recv @Int
    Ix.return n

andOffer ::
  IProg
    effs
    Protocol
    ProtocolG
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
  IProg
    effs
    Protocol
    ProtocolG
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
  IProg '[] Protocol ProtocolG p1 '[End] a ->
  IProg '[] Protocol ProtocolG p2 '[End] b ->
  IProg '[] IIdentity IVoid () () (a, b)
connect (Value x) (Value y) = Ix.return (x, y)
connect (ImpureT (Recv) k1) (ImpureT ((Send a)) k2) = connect (runIKleisliTupled k1 a) (runIKleisliTupled k2 ())
connect (ImpureT ((Send a)) k1) (ImpureT (Recv) k2) = connect (runIKleisliTupled k1 ()) (runIKleisliTupled k2 a)
connect (ScopeT (Sel1 act1) k1) (ScopeT (Offer act2 _) k2) = Ix.do
  (a, b) <- connect act1 act2
  connect (runIKleisliTupled k1 a) (runIKleisliTupled k2 b)
connect (ScopeT (Sel2 act1) k1) (ScopeT (Offer _ act2) k2) = Ix.do
  (a, b) <- connect act1 act2
  connect (runIKleisliTupled k1 a) (runIKleisliTupled k2 b)
connect (ScopeT (Offer act1 _) k1) (ScopeT (Sel1 act2) k2) = Ix.do
  (a, b) <- connect act1 act2
  connect (runIKleisliTupled k1 a) (runIKleisliTupled k2 b)
connect (ScopeT (Offer _ act1) k1) (ScopeT (Sel2 act2) k2) = Ix.do
  (a, b) <- connect act1 act2
  connect (runIKleisliTupled k1 a) (runIKleisliTupled k2 b)
connect (ScopeT (LoopSUnbounded act1) k1) (ScopeT (LoopCUnbounded act2) k2) = Ix.do
  (a, b) <- go ([], [])
  connect (runIKleisliTupled k1 a) (runIKleisliTupled k2 b)
  where
    go (r1, r2) = Ix.do
      (a, b) <- connect act1 act2
      case a of
        Nothing -> Ix.return (r1, b:r2)
        Just a' -> go (a': r1, b:r2)


connect _ _ = error "Procol.connect: internal tree error"


connect' ::
  (Dual p1 ~ p2, Dual p2 ~ p1) =>
  IProg effs Protocol ProtocolG p1 '[End] a ->
  IProg effs Protocol ProtocolG p2 '[End] b ->
  IProg effs IIdentity IVoid () () (a, b)
connect' (Value x) (Value y) = Ix.return (x, y)
connect' (ImpureT (Recv) k1) (ImpureT ((Send a)) k2) = connect' (runIKleisliTupled k1 a) (runIKleisliTupled k2 ())
connect' (ImpureT ((Send a)) k1) (ImpureT (Recv) k2) = connect' (runIKleisliTupled k1 ()) (runIKleisliTupled k2 a)
connect' (ScopeT (Sel1 act1) k1) (ScopeT (Offer act2 _) k2) = Ix.do
  (a, b) <- connect' act1 act2
  connect' (runIKleisliTupled k1 a) (runIKleisliTupled k2 b)
connect' (ScopeT (Sel2 act1) k1) (ScopeT (Offer _ act2) k2) = Ix.do
  (a, b) <- connect' act1 act2
  connect' (runIKleisliTupled k1 a) (runIKleisliTupled k2 b)
connect' (ScopeT (Offer act1 _) k1) (ScopeT (Sel1 act2) k2) = Ix.do
  (a, b) <- connect' act1 act2
  connect' (runIKleisliTupled k1 a) (runIKleisliTupled k2 b)
connect' (ScopeT (Offer _ act1) k1) (ScopeT (Sel2 act2) k2) = Ix.do
  (a, b) <- connect' act1 act2
  connect' (runIKleisliTupled k1 a) (runIKleisliTupled k2 b)
connect' (ScopeT (LoopSUnbounded act1) k1) (ScopeT (LoopCUnbounded act2) k2) = Ix.do
  (a, b) <- go ([], [])
  connect' (runIKleisliTupled k1 a) (runIKleisliTupled k2 b)
  where
    go (r1, r2) = Ix.do
      (a, b) <- connect' act1 act2
      case a of
        Nothing -> Ix.return (r1, b:r2)
        Just a' -> go (a': r1, b:r2)
connect' (ScopeT (LoopCUnbounded act1) k1) (ScopeT (LoopSUnbounded act2) k2) = Ix.do
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
