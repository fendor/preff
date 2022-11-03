{-# LANGUAGE QualifiedDo #-}
module Parameterised.Protocol where

import Data.Kind
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
    Sel1 :: Protocol (a :| b) a ()
    Sel2 :: Protocol (a :| b) b ()
    Offer :: Protocol a p () -> Protocol b p () -> Protocol (a :& b) p ()

type family Dual proc where
  Dual (a :! p) = a :? Dual p
  Dual (a :? p) = a :! Dual p
  -- Dual (a :| b) = Dual a :& Dual b
  -- Dual (a :& b) = Dual a :| Dual a
  Dual End = End

send :: a -> Sem (Protocol :+: IIdentity) '(a :! p, sr) '(p, sr) ()
send a = Op (Inl (Send a)) (IKleisliTupled Utils.return)

recv :: Sem (Protocol :+: IIdentity) '(a :? p, sr) '(p, sr) a
recv = Op (Inl Recv)  (IKleisliTupled Utils.return)

sel1 :: Sem (Protocol :+: IIdentity) '(a :| b, sr) '(a, sr) ()
sel1 = Op (Inl Sel1)  (IKleisliTupled Utils.return)

sel2 :: Sem (Protocol :+: IIdentity) '(a :| b, sr) '(b, sr) ()
sel2 = Op (Inl Sel2)  (IKleisliTupled Utils.return)

-- simpleProtocol :: Sem (Protocol :+: IIdentity) '(p, sr) '(Int :! String :? p, sr) String
simpleServer ::
  Sem
    (Protocol :+: IIdentity)
    '(Int :! (String :? p), sr)
    '(p, sr)
    String
simpleServer = Ix.do
  send @Int 5
  s <- recv @String
  Ix.return s

simpleClient ::
  Sem
    (Protocol :+: IIdentity)
    '(Int :? (String :! p), sr)
    '(p, sr)
    ()
simpleClient = Ix.do
  n <- recv @Int
  send (show $ n * 25)

choice = Ix.do
  send @Int 5
  sel1
  n <- recv @Int
  Ix.return n

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
--   connect (Op (Inr op1) k1) (Op (Inr op2) k2) = connect (Op op1 undefined) (Op op2 undefined)
--   connect sl@(Value _) (Op (Inr op2) k2) =

-- instance Connect p => Connect (a :! p) where
--   type Succ (a :! p) = p
--   -- type Succ2 (a :=)

--   connect (Op (Inl (Send (a :: a))) k1) (Op (Inl Recv) k2) =
--     connect (runIKleisliTupled k1 ()) (runIKleisliTupled k2 a)
--   -- connect sl@(Op (Inl _) _) (Op (Inr op) k2) = Op op $ \x -> connect sl (runIKleisliTupled k2 x)
--   connect _ _ = undefined

connect :: Dual p1 ~ q1 =>
  Sem (Protocol :+: IIdentity) '(p1, ()) '(End, ()) a ->
  Sem (Protocol :+: IIdentity) '(q1, ()) '(End, ()) b ->
  (a, b)
connect (Value x) (Value y) = (x, y)
connect (Op (Inl Recv) k1) (Op (Inl (Send a)) k2) = connect (runIKleisliTupled k1 a) (runIKleisliTupled k2 ())
connect (Op (Inl (Send a)) k1) (Op (Inl Recv) k2) = connect (runIKleisliTupled k1 ()) (runIKleisliTupled k2 a)


