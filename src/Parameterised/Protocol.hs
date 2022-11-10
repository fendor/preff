{-# LANGUAGE QualifiedDo #-}
module Parameterised.Protocol where

import Utils
import qualified Utils as Ix
import Unsafe.Coerce

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
    Sel1 :: Protocol (a :| b) a ()
    Sel2 :: Protocol (a :| b) b ()

data ProtocolG m p p' q' q x x' where
    Offer ::
      m '(a, sr1) '(c, sr2) x ->
      m '(b, sr1) '(c, sr2) x ->
      ProtocolG m '(a :& b, sr1) '(a :& b, sr1) '(c, sr2) '(c, sr2) x x

type family Dual proc where
  Dual (a :! p) = a :? Dual p
  Dual (a :? p) = a :! Dual p
  Dual (a :| b) = Dual a :& Dual b
  Dual (a :& b) = Dual a :| Dual b
  Dual End = End

send :: forall a effs g p sr.
  a ->
  IProg (Op (Protocol : effs)) g '(a :! p, sr) '(p, sr) ()
send a = Impure (OHere (Send a)) (IKleisliTupled Utils.return)

-- recv :: IProg (Protocol :+: IIdentity) ProtocolG '(a :? p, sr) '(p, sr) a
recv :: forall a p effs g sr .
  IProg (Op (Protocol : effs)) g '(a :? p, sr) '(p, sr) a
recv = Impure (OHere Recv)  (IKleisliTupled Utils.return)

-- sel1 :: IProg (Protocol :+: IIdentity) ProtocolG '(a :| b, sr) '(a, sr) ()
sel1 ::
  IProg (Op (Protocol : effs)) g '(sl2 :| b, sr) '(sl2, sr) ()
sel1 = Impure (OHere Sel1)  (IKleisliTupled Utils.return)

-- sel2 :: IProg (Protocol :+: IIdentity) ProtocolG '(a :| b, sr) '(b, sr) ()
sel2 ::
  IProg (Op (Protocol : effs)) g '(a :| sl2, sr) '(sl2, sr) ()
sel2 = Impure (OHere Sel2)  (IKleisliTupled Utils.return)

offer ::
  IProg f ProtocolG '(a1, sr1) '(c, sr2) a2 ->
  IProg f ProtocolG '(b, sr1) '(c, sr2) a2 ->
  IProg f ProtocolG '(a1 :& b, sr1) '(c, sr2) a2
offer s1 s2 = Scope (Offer s1 s2) emptyCont

simpleServer = Ix.do
  send @Int 5
  s <- recv @String
  Ix.return s

simpleClient = Ix.do
  n <- recv @Int
  send (show $ n * 25)

choice = Ix.do
  send @Int 5
  sel1
  n <- recv @Int
  Ix.return n

andOffer = Ix.do
  n <- recv @Int
  offer
    (Ix.do
      send @Int n)
    (Ix.do
      send @Int n)
  Ix.return ()

choice2 = Ix.do
  n <- recv @Int
  ifThenElse (n < 0)
    (Ix.do
      sel1
      x <- recv @String
      Ix.return x
    )
    (Ix.do
      sel2
      send @String "Test"
      x <- recv @String
      Ix.return x
    )

connect :: forall p1 p2 srp1 srp2 srq1 srq2 a b.
  (Dual p1 ~ p2, Dual p2 ~ p1) =>
  IProg (Op [Protocol, IIdentity]) ProtocolG '(p1, srp1) '(End, srq1) a ->
  IProg (Op [Protocol, IIdentity]) ProtocolG '(p2, srp2) '(End, srq2) b ->
  (a, b)
connect (Pure x) (Pure y) = (x, y)
connect (Impure (OHere Recv) k1)     (Impure (OHere (Send a)) k2) = connect (runIKleisliTupled k1 a) (runIKleisliTupled k2 ())
connect (Impure (OHere (Send a)) k1) (Impure (OHere Recv) k2) = connect (runIKleisliTupled k1 ()) (runIKleisliTupled k2 a)
connect (Impure (OHere Sel1) k1)     (Scope (Offer act _) k2) =
  connect act1 act2
  where
    act1 = runIKleisliTupled k1 ()
    act2 = unsafeCoerce act
connect (Impure (OHere Sel2) k1)     (Scope (Offer act _) k2) =
  connect act1 act2
  where
    act1 = runIKleisliTupled k1 ()
    act2 = unsafeCoerce act
connect (Scope (Offer act _) k1)    (Impure (OHere Sel1) k2) =
  connect act1 act2
  where
    act1 = unsafeCoerce act
    act2 = runIKleisliTupled k2 ()
connect (Scope (Offer _ act) k1)    (Impure (OHere Sel2) k2) =
  connect act1 act2
  where
    act1 = unsafeCoerce act
    act2 = runIKleisliTupled k2 ()
connect (Pure _) (Impure _ _) = error "Procol.connect: internal tree error"
connect (Pure _) (Scope _ _) = error "Procol.connect: internal tree error"
connect (Impure (OThere _) _) _ = error "Procol.connect: internal tree error"
connect (Impure (OHere Recv) _) (Scope _ _) = error "Procol.connect: internal tree error"
connect (Scope (Offer _ _) _) (Scope _ _) = error "Protocol.connect: internal tree error"
connect (Scope (Offer _ _) _) (Impure (OThere _) _) = error "Protocol.connect: internal tree error"
connect (Impure (OHere (Send _)) _) (Scope _ _) = error "Protocol.connect: internal tree error"
connect (Impure (OHere (Send _)) _) (Impure (OThere _) _) = error "Protocol.connect: internal tree error"
connect (Impure (OHere Sel1) _) (Impure _ _) = error "Protocol.conncet: internal tree error"
connect (Impure (OHere Sel2) _) (Impure _ _) = error "Protocol.conncet: internal tree error"
connect (Impure (OHere Recv) _) (Impure (OThere _) _) = error "Protocol.conncet: internal tree error"
-- connect _                           _                       = error "Protocol.connect: internal tree error"
