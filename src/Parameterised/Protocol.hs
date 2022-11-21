{-# LANGUAGE QualifiedDo #-}

module Parameterised.Protocol where

import Unsafe.Coerce
import Utils
import qualified Utils as Ix
import Data.Kind

-- type End :: Type
data End
data S a
data R a
data C a b
data O a b

type Protocol :: forall k .
    [k] -> [k] -> Type -> Type
data Protocol p q r where
    Send :: a -> Protocol (S a : p) p ()
    Recv :: Protocol (R a : p) p a

type ProtocolG :: forall k.
    ([k] -> [k] -> Type -> Type) ->
    [k] -> [k] -> [k] -> [k] -> Type -> Type -> Type
data ProtocolG m p p' q' q x x' where
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
    Dual '[End] = '[End]

send ::
    forall a effs g p sr.
    a ->
    IProg effs Protocol g (S a : p) p ()
send a = ImpureT ((Send a)) (IKleisliTupled Utils.return)

-- recv :: IProg (Protocol :+: IIdentity) ProtocolG '(a :? p, sr) '(p, sr) a
recv ::
    forall a p effs g .
    IProg effs Protocol g (R a : p) p a
recv = ImpureT ( Recv) (IKleisliTupled Utils.return)

-- sel1 ::
--     IProg effs f ProtocolG '[a] '[End] a ->
--     IProg effs f ProtocolG (C a b : r) r a
sel1 act = ScopeT (Sel1 act) (IKleisliTupled Utils.return)


-- sel2 ::
--     IProg effs f ProtocolG b End a2 ->
--     IProg effs f ProtocolG (C a b) r a2
sel2 act = ScopeT (Sel2 act) (IKleisliTupled Utils.return)

-- offer ::
--     IProg effs f ProtocolG a End a2 ->
--     IProg effs f ProtocolG b End a2 ->
--     IProg effs f ProtocolG (O a b : c) c a2
offer s1 s2 = ScopeT (Offer s1 s2) emptyCont

simpleServer = Ix.do
    send @Int 5
    s <- recv @String
    Ix.return s

simpleClient = Ix.do
    n <- recv @Int
    send (show $ n * 25)


choice = Ix.do
    send @Int 5
    sel1 $ Ix.do
        n <- recv @Int
        Ix.return n

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
connect (ImpureT (Recv) k1)     (ImpureT ( (Send a)) k2) = connect (runIKleisliTupled k1 a) (runIKleisliTupled k2 ())
connect (ImpureT ((Send a)) k1) (ImpureT ( Recv) k2) = connect (runIKleisliTupled k1 ()) (runIKleisliTupled k2 a)
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
connect _ _ = error "Procol.connect: internal tree error"

-- connect _                           _                       = error "Protocol.connect: internal tree error"
