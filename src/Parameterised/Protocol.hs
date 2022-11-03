{-# LANGUAGE QualifiedDo #-}
module Parameterised.Protocol where

import Data.Kind
import Utils
import qualified Utils as Ix

type End :: Type
data End

type (:!) :: forall k . Type -> k -> Type
data (:!) a r

infixr 5 :?
type (:?) :: forall k . Type -> k -> Type
data (:?) a r

type (:|) :: forall k . k -> k -> Type
data (:|) sl sr

type (:&) :: forall k . k -> k -> Type
data (:&) sl sr

data Protocol p q r where
    Send :: a -> Protocol (a :! p) p ()
    Recv :: Protocol (a :? p) p a
    Sel1 :: Protocol (a :| b) a ()
    Sel2 :: Protocol (a :| b) b ()

type family Dual proc where
  Dual (a :! p) = a :? Dual p
  Dual (a :? p) = a :! Dual p
  Dual (a :| b) = Dual a :& Dual b
  Dual (a :& b) = Dual a :| Dual a
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
simpleProtocol :: forall {k} {p} {sr :: k}.
  Sem
    (Protocol :+: IIdentity)
    '(Int :! (String :? p), sr)
    '(p, sr)
    String
simpleProtocol = Ix.do
  send @Int 5
  s <- recv @String
  Ix.return s

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

connect :: Dual p ~ q =>
  Sem (Protocol :+: eff) '(q, sr) '(End, sr) a ->
  Sem (Protocol :+: eff) '(p, sr) '(End, sr) b ->
  Sem eff sr sr (a, b)
connect a b = undefined