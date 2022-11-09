{-# LANGUAGE QualifiedDo #-}
module Parameterised.Protocol where

import Data.Kind
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
      ProtocolG m '((a :& b), sr1) '((a :& b), sr1) '(c, sr2) '(c, sr2) x x

type family Dual proc where
  Dual (a :! p) = a :? Dual p
  Dual (a :? p) = a :! Dual p
  Dual (a :| b) = Dual a :& Dual b
  Dual (a :& b) = Dual a :| Dual b
  Dual End = End

send :: a -> IProg (Protocol :+: IIdentity) ProtocolG '(a :! p, sr) '(p, sr) ()
send a = Impure (OInl (Send a)) (IKleisliTupled Utils.return)

recv :: IProg (Protocol :+: IIdentity) ProtocolG '(a :? p, sr) '(p, sr) a
recv = Impure (OInl Recv)  (IKleisliTupled Utils.return)

sel1 :: IProg (Protocol :+: IIdentity) ProtocolG '(a :| b, sr) '(a, sr) ()
sel1 = Impure (OInl Sel1)  (IKleisliTupled Utils.return)

sel2 :: IProg (Protocol :+: IIdentity) ProtocolG '(a :| b, sr) '(b, sr) ()
sel2 = Impure (OInl Sel2)  (IKleisliTupled Utils.return)

offer s1 s2 = Scope (Offer s1 s2) emptyCont

-- simpleProtocol :: Sem (Protocol :+: IIdentity) '(p, sr) '(Int :! String :? p, sr) String
simpleServer ::
  IProg
    (Protocol :+: IIdentity)
    ProtocolG
    '(Int :! (String :? p), sr)
    '(p, sr)
    String
simpleServer = Ix.do
  send @Int 5
  s <- recv @String
  Ix.return s

simpleClient ::
  IProg
    (Protocol :+: IIdentity)
    ProtocolG
    '(Int :? (String :! p), sr)
    '(p, sr)
    ()
simpleClient = Ix.do
  n <- recv @Int
  send (show $ n * 25)

choice :: forall {k1} {k2} {p} {b :: k2} {sr :: k1}.
  IProg
    (Protocol :+: IIdentity)
    ProtocolG
    '(Int :! ((Int :? p) :| b), sr)
    '(p, sr)
    Int
choice = Ix.do
  send @Int 5
  sel1
  n <- recv @Int
  Ix.return n

andOffer :: forall k (sr :: k).
  IProg
    (Protocol :+: IIdentity)
    ProtocolG
    '(Int :? ((Int :! End) :& (Int :! End)), sr)
    '(End, sr)
    ()
andOffer = Ix.do
  n <- recv @Int
  offer
    (Ix.do
      send @Int n)
    (Ix.do
      send @Int n)
  Ix.return ()

type PingPong p = Int :? p

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

-- class Connect p1 where
--   type Succ p1
--   connect :: (q1 ~ Dual p1, q1 ~ Dual p1) => -- , Dual (Succ p1) ~ q2, Dual q2 ~ Succ p1) =>
--     Sem (Protocol :+: eff1) '(p1, sr1) '(Succ p1, sr1) a ->
--     Sem (Protocol :+: eff2) '(q1, sr2) '(q2, sr2) b ->
--     (Sem eff1 sr1 sr1 a, Sem eff2 sr2 sr2 b)

-- instance Connect End End where
--   connect (Value x) (Value y) = Ix.return (x, y)
--   connect (Op (OInr op1) k1) (Op (OInr op2) k2) = connect (Op op1 undefined) (Op op2 undefined)
--   connect sl@(Value _) (Op (OInr op2) k2) =

-- instance Connect p => Connect (a :! p) where
--   type Succ (a :! p) = p
--   -- type Succ2 (a :=)

--   connect (Op (OInl (Send (a :: a))) k1) (Op (OInl Recv) k2) =
--     connect (runIKleisliTupled k1 ()) (runIKleisliTupled k2 a)
--   -- connect sl@(Op (OInl _) _) (Op (OInr op) k2) = Op op $ \x -> connect sl (runIKleisliTupled k2 x)
--   connect _ _ = undefined

connect :: forall p1 p2 sr a b.
  (Dual p1 ~ p2, Dual p2 ~ p1) =>
  IProg (Protocol :+: IIdentity) ProtocolG '(p1, sr) '(End, sr) a ->
  IProg (Protocol :+: IIdentity) ProtocolG '(p2, sr) '(End, sr) b ->
  (a, b)
connect (Pure x) (Pure y) = (x, y)
connect (Impure (OInl Recv) k1)     (Impure (OInl (Send a)) k2) = connect (runIKleisliTupled k1 a) (runIKleisliTupled k2 ())
connect (Impure (OInl (Send a)) k1) (Impure (OInl Recv) k2) = connect (runIKleisliTupled k1 ()) (runIKleisliTupled k2 a)
connect (Impure (OInl Sel1) k1)     (Scope (Offer act _) k2) =
  connect act1 act2
  where
    act1 = runIKleisliTupled k1 ()
    act2 = unsafeCoerce act
connect (Impure (OInl Sel2) k1)     (Scope (Offer act _) k2) =
  connect act1 act2
  where
    act1 = runIKleisliTupled k1 ()
    act2 = unsafeCoerce act
connect (Scope (Offer act _) k1)    (Impure (OInl Sel1) k2) =
  connect act1 act2
  where
    act1 = unsafeCoerce act
    act2 = runIKleisliTupled k2 ()
connect (Scope (Offer _ act) k1)    (Impure (OInl Sel2) k2) =
  connect act1 act2
  where
    act1 = unsafeCoerce act
    act2 = runIKleisliTupled k2 ()
connect (Pure _) (Impure _ _) = error "Procol.connect: internal tree error"
connect (Pure _) (Scope _ _) = error "Procol.connect: internal tree error"
connect (Impure (OInr _) _) _ = error "Procol.connect: internal tree error"
connect (Impure (OInl Recv) _) (Scope _ _) = error "Procol.connect: internal tree error"
connect (Scope (Offer _ _) _) (Scope _ _) = error "Protocol.connect: internal tree error"
connect (Scope (Offer _ _) _) (Impure (OInr _) _) = error "Protocol.connect: internal tree error"
connect (Impure (OInl (Send _)) _) (Scope _ _) = error "Protocol.connect: internal tree error"
connect (Impure (OInl (Send _)) _) (Impure (OInr _) _) = error "Protocol.connect: internal tree error"
connect (Impure (OInl Sel1) _) (Impure _ _) = error "Protocol.conncet: internal tree error"
connect (Impure (OInl Sel2) _) (Impure _ _) = error "Protocol.conncet: internal tree error"
connect (Impure (OInl Recv) _) (Impure (OInr _) _) = error "Protocol.conncet: internal tree error"
-- connect _                           _                       = error "Protocol.connect: internal tree error"

