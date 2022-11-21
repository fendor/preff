{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE QualifiedDo #-}
{-# OPTIONS_GHC -Wno-missing-signatures #-}

module Parameterised.State where

import Data.Kind
import Data.Proxy
import GHC.TypeLits
import GHC.Types
import Unsafe.Coerce
import Utils
import qualified Utils as Ix
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

data StateG m p p' q' q x x' where
    Fork :: (AcceptableList p1 q1 p2) => m p2 q2 a -> StateG m p1 p2 q2 q1 a (Future a)
    Finish :: m p2 q2 a -> StateG m p p q p a a

type Token :: Type -> Ix.Nat -> Type
newtype Token t n = Token ()

data Future a = Future

put a b = Impure (OHere $ Put a b) emptyCont

alloc a = Impure (OHere $ Alloc a) emptyCont

get a = Impure (OHere $ Get a) emptyCont

fork s = Scope (Fork s) emptyCont

finish s = Scope (Finish s) emptyCont

data StateA p q a where
    PutA :: x -> StateA p x ()
    GetA :: StateA p p p

putAI ::
    forall p ind effs g ps qs.
    ( KnownNat ind
    , FindEff StateA effs ~ ind
    , Write ind p ps ~ qs
    , Assume ind qs ~ p
    ) =>
    p ->
    IProg effs g ps qs ()
putAI p = Impure (inj (Proxy :: Proxy ind) $ PutA p) emptyCont

getAI ::
    forall ind effs g ps p.
    ( KnownNat ind
    , FindEff StateA effs ~ ind
    , Assume ind ps ~ p
    ) =>
    IProg effs g ps ps p
getAI = Impure (inj (Proxy :: Proxy ind) GetA) emptyCont

stateChangeExp ::
    forall ind p j effs ps qs sr p1.
    ( KnownNat ind
    , FindEff StateA effs ~ ind
    , ind ~ 0
    , Assume ind ps ~ String
    , Write ind Int ps ~ qs
    -- , qs ~ (Int: sr)
    ) =>
    IProg effs StateAG ps qs String
-- stateChangeExp :: IProg '[StateA] StateAG '[String] '[Int] String
stateChangeExp = Ix.do
    s <- getAI
    -- putAI ("Test" :: String)
    putAI (5 :: Int)
    -- putAI (3 :: Int)
    x <- localAG' (+ (1 :: Int)) $ getAI
    Ix.return $ s ++ show x

runStateChangeExp = run $ runStateAIG "Test" stateChangeExp

localAG' ::
    (p -> p') ->
    IProg f StateAG (p' : sr1) (q : sr2) a ->
    IProg f StateAG (p : sr1) (p : sr2) a
localAG' f act = Scope (LocalAG f act) emptyCont

data StateAG m p p' q' q x x' where
    LocalAG ::
        (p -> p') ->
        m (p' : sr1) (q : sr2) x ->
        StateAG m (p : sr1) (p' : sr1) (q' : sr2) (p : sr2) x x

runStateAIG ::
    p ->
    IProg (StateA : eff) StateAG (p : sr1) (q : sr2) a ->
    IProg eff IVoid sr1 sr2 (a, q)
runStateAIG p (Pure x) = Ix.return (x, p)
runStateAIG p (Impure (OHere GetA) k) =
    runStateAIG p (runIKleisliTupled k p)
runStateAIG _ (Impure (OHere (PutA q)) k) =
    runStateAIG q (runIKleisliTupled k ())
runStateAIG p (Impure (OThere op) k) =
    Impure op $ IKleisliTupled $ \x -> runStateAIG p (runIKleisliTupled k x)
runStateAIG p (Scope (LocalAG f m) k) = Ix.do
    (x, _q) <- runStateAIG (f p) m
    runStateAIG p (runIKleisliTupled k x)

runStateAI ::
    p ->
    IProg (StateA : eff) IVoid (p : sr1) (q : sr2) a ->
    IProg eff IVoid sr1 sr2 (a, q)
runStateAI p (Pure x) = Ix.return (x, p)
runStateAI p (Impure (OHere GetA) k) =
    runStateAI p (runIKleisliTupled k p)
runStateAI _ (Impure (OHere (PutA q)) k) =
    runStateAI q (runIKleisliTupled k ())
runStateAI p (Impure (OThere op) k) =
    Impure op $ IKleisliTupled $ \x -> runStateAI p (runIKleisliTupled k x)
runStateAI _p (Scope _ _) = error "GHC is not exhaustive"

genericState ::
    ( FindEff StateA effs ~ ind
    , Write ind Int p ~ q
    ) =>
    IProg effs g p q ()
genericState = undefined

-- putA ::
--   ( SMember StateA () q effs ps qs
--   ) =>
--   q ->
--   IProg effs g ps qs ()
-- putA q = Impure (inj (PutA q) :: Op effs ps qs ()) emptyCont
