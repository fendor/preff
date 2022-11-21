{-# LANGUAGE QualifiedDo #-}

module Parameterised.Protocol where

import Unsafe.Coerce
import Utils
import qualified Utils as Ix

-- type End :: Type
data End

-- type (:!) :: forall k . Type -> k -> Type
data (:!) a r
infixr 5 :!

-- type (:?) :: forall k . Type -> k -> Type
data (:?) a r
infixr 5 :?

-- type (:|) :: forall k . k -> k -> Type
data (:|) sl sr

-- type (:&) :: forall k . k -> k -> Type
data (:&) sl sr

data Protocol p q r where
    Send :: a -> Protocol (a :! p) p ()
    Recv :: Protocol (a :? p) p a

data ProtocolG m p p' q' q x x' where
    Sel1 ::
        m a c x ->
        ProtocolG m (a :| b) a c c x x
    Sel2 ::
        m b c x ->
        ProtocolG m (a :| b) b c c x x
    Offer ::
        m a c x ->
        m b c x ->
        ProtocolG m (a :& b) (a :& b) c c x x

type family Dual proc where
    Dual (a :! p) = a :? Dual p
    Dual (a :? p) = a :! Dual p
    Dual (a :| b) = Dual a :& Dual b
    Dual (a :& b) = Dual a :| Dual b
    Dual End = End

send ::
    forall a effs g p sr.
    a ->
    IProg effs Protocol g (a :! p) p ()
send a = ImpureT ((Send a)) (IKleisliTupled Utils.return)

-- recv :: IProg (Protocol :+: IIdentity) ProtocolG '(a :? p, sr) '(p, sr) a
recv ::
    forall a p effs g .
    IProg effs Protocol g (a :? p) p a
recv = ImpureT ( Recv) (IKleisliTupled Utils.return)


sel1 ::
    IProg effs f ProtocolG a r a ->
    IProg effs f ProtocolG (a :| b) r a
sel1 act = ScopeT (Sel1 act) (IKleisliTupled Utils.return)

-- sel2 :: IProg (Protocol :+: IIdentity) ProtocolG '(a :| b, sr) '(b, sr) ()

sel2 ::
    IProg effs f ProtocolG b r a2 ->
    IProg effs f ProtocolG (a :| b) r a2
sel2 act = ScopeT (Sel2 act) (IKleisliTupled Utils.return)

offer ::
    IProg effs f ProtocolG a c a2 ->
    IProg effs f ProtocolG b c a2 ->
    IProg effs f ProtocolG (a :& b) c a2
offer s1 s2 = ScopeT (Offer s1 s2) emptyCont

simpleServer = Ix.do
    send @Int 5
    s <- recv @String
    Ix.return s

simpleClient = Ix.do
    n <- recv @Int
    send (show $ n * 25)


choice ::
    IProg effs Protocol ProtocolG (Int :! ((Int :? k2) :| b)) k2 (Int :? k2)
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
    IProg '[] Protocol ProtocolG p1 End a ->
    IProg '[] Protocol ProtocolG p2 End b ->
    (a, b)
connect (Value x) (Value y) = (x, y)
connect (ImpureT (Recv) k1)     (ImpureT ( (Send a)) k2) = connect (runIKleisliTupled k1 a) (runIKleisliTupled k2 ())
connect (ImpureT ((Send a)) k1) (ImpureT ( Recv) k2) = connect (runIKleisliTupled k1 ()) (runIKleisliTupled k2 a)
connect (ScopeT (Sel1 act1) k1) (ScopeT (Offer act2 _) k2) =
    connect act1 act2
connect (ScopeT (Sel2 act1) k1) (ScopeT (Offer act2 _) k2) =
    connect act1 act2
connect (ScopeT (Offer act1 _) k1) (ScopeT (Sel1 act2) k2) =
    connect act1 act2
connect (ScopeT (Offer _ act1) k1) (ScopeT (Sel2 act2) k2) =
    connect act1 act2
connect _ _ = error "Procol.connect: internal tree error"

-- connect _                           _                       = error "Protocol.connect: internal tree error"
