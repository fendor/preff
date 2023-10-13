module PrEff.Parameterised.Session where

import Data.Kind
import PrEff hiding (send)
import qualified PrEff
import qualified Control.IxMonad as Ix
import PrEff.Simple.State

data End
data S a
data R a
data C a b
data O a b
data SL n a
data CL n a
data SLU a
data CLU a

type Session ::
  forall k.
  [k] ->
  [k] ->
  Type ->
  Type
data Session p q r where
  Send :: a -> Session (S a : p) p ()
  Recv :: Session (R a : p) p a

data instance ScopeE Session m p p' q' q x' x where
  Offer ::
    m a '[End] x ->
    m b '[End] x ->
    ScopeE Session m (O a b : c) '[O a b] '[End] c x x
  Sel1 ::
    m a '[End] x ->
    ScopeE Session m (C a b : c) a '[End] c x x
  Sel2 ::
    m b '[End] x ->
    ScopeE Session m (C a b : c) b '[End] c x x
  LoopSUnbounded ::
    m a '[End] (Maybe x) ->
    ScopeE Session m (SLU a : c) a '[End] c (Maybe x) [x]
  LoopCUnbounded ::
    m a '[End] x ->
    ScopeE Session m (CLU a : r) a '[End] r x [x]

-- myweave :: Functor ctx =>
--   ctx () ->
--   -- natural transformation
--   (forall r u v. ctx (m u v r) -> n u v (ctx r)) ->
--   ScopeE Session m p p' q' q x x' ->
--   ScopeE Session n p p' q' q (ctx x) (ctx x')
-- myweave ctx nt = \case
--   LoopCUnbounded m ->
--     let
--       n = nt (m <$ ctx)
--     in LoopCUnbounded n
--   LoopSUnbounded m ->
--     let
--       n = nt (m <$ ctx)
--     in LoopSUnbounded n
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

type family Dual' proc
type instance Dual' (R a) = S a
type instance Dual' (S a) = R a
type instance Dual' (O a b) = C (Dual a) (Dual b)
type instance Dual' (C a b) = O (Dual a) (Dual b)
type instance Dual' (CLU a) = SLU (Dual a)
type instance Dual' (SLU a) = CLU (Dual a)
type instance Dual' End = End

type family Dual proc where
  Dual '[] = '[]
  Dual (x: xs) = Dual' x : Dual xs

send ::
  forall a f p.
  a ->
  PrEff f Session (S a : p) p ()
send a = sendP (Send a)

recv ::
  forall a p f.
  PrEff f Session (R a : p) p a
recv = sendP Recv

sel1 ::
  PrEff f Session a '[End] x ->
  PrEff f Session (C a b : p) p x
sel1 act = sendScoped (Sel1 act)

sel2 ::
  PrEff f Session b '[End] x ->
  PrEff f Session (C a b : p) p x
sel2 act = sendScoped (Sel2 act)

offer ::
  PrEff f Session a '[End] x ->
  PrEff f Session b '[End] x ->
  PrEff f Session (O a b : p) p x
offer s1 s2 = sendScoped (Offer s1 s2)

loopS ::
  PrEff effs Session a '[End] (Maybe x) ->
  PrEff effs Session (SLU a: p) p [x]
loopS act = sendScoped (LoopSUnbounded act)

loopC ::
  PrEff f Session a '[End] x ->
  PrEff f Session (CLU a: p) p [x]
loopC act = sendScoped (LoopCUnbounded act)

simpleServer :: PrEff f Session '[S String, R String, End] '[End] String
simpleServer = Ix.do
  send "Ping"
  s <- recv @String
  pure s

simpleClient :: PrEff f Session '[R String, S String, End] '[End] String
simpleClient = Ix.do
  a <- recv
  send "Pong"
  pure a

stringOrInt :: PrEff f Session [O '[R String, End] '[R Int, End], End] '[End] String
stringOrInt = Ix.do
  offer
    ( Ix.do
        n <- recv @String
        pure n
    )
    ( Ix.do
        n <- recv @Int
        pure (show n)
    )

data RandomNumber a where
  GetNumber :: RandomNumber Int

getNumber :: Member RandomNumber f => PrEff f s p p Int
getNumber = PrEff.send GetNumber

runRandomNumber :: ScopedEffect s => PrEff (RandomNumber : effs) s p q x -> PrEff effs s p q x
runRandomNumber = interpret $ \case
  -- Chosen by fair dice roll
  GetNumber -> pure 4

guessNumberServer ::
  Member RandomNumber f =>
  PrEff f Session '[SLU '[R Int, End], End] '[End] Int
guessNumberServer = Ix.do
  num <- getNumber
  attempts <- loopS $ Ix.do
    n <- recv
    if n == num
      then pure Nothing
      else pure (Just ())

  pure $ length attempts


serverLoop :: Member (State Int) f => PrEff f Session (SLU '[S Int, R Int, End] : r) r [Int]
serverLoop = Ix.do
  loopS $ Ix.do
    x <- get
    send x
    n :: Int <- recv
    put n
    if n < 10
      then
        pure Nothing
      else
        pure $ Just n

clientLoop :: PrEff f Session (CLU '[R Int, S Int, End] : r) r [()]
clientLoop = Ix.do
  loopC $ Ix.do
    n :: Int <- recv
    send (n - 1)
    pure ()

choice ::
  PrEff
    f
    Session
    (S Int : C '[R Int, End] b : k)
    k
    Int
choice = Ix.do
  send @Int 5
  sel1 $ Ix.do
    n <- recv @Int
    pure n

andOffer ::
  PrEff
    f
    Session
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
  pure ()

choice2 ::
  PrEff
    f
    Session
    (R Int : C '[R String, End] '[S String, R String, End] : k)
    k
    String
choice2 = Ix.do
  n <- recv @Int
  if
    (n < 0)
    then Ix.do
        sel1 $ Ix.do
          x <- recv @String
          pure x

    else Ix.do
        sel2 $ Ix.do
          send @String "Test"
          x <- recv @String
          pure x


simpleLoopingClientServer :: Member (State Int) f => PrEff f IVoid () () ([()], [Int])
simpleLoopingClientServer = connect' clientLoop serverLoop

connect ::
  (Dual p1 ~ p2, Dual p2 ~ p1) =>
  PrEff '[] Session p1 '[End] a ->
  PrEff '[] Session p2 '[End] b ->
  PrEff '[] IVoid () () (a, b)
connect (Value x) (Value y) = pure (x, y)
connect (ImpureP Recv k1) (ImpureP (Send a) k2) = connect (runIKleisli k1 a) (runIKleisli k2 ())
connect (ImpureP (Send a) k1) (ImpureP Recv k2) = connect (runIKleisli k1 ()) (runIKleisli k2 a)
connect (ScopedP (Sel1 act1) k1) (ScopedP (Offer act2 _) k2) = do
  (a, b) <- connect act1 act2
  connect (runIKleisli k1 a) (runIKleisli k2 b)
connect (ScopedP (Sel2 act1) k1) (ScopedP (Offer _ act2) k2) = do
  (a, b) <- connect act1 act2
  connect (runIKleisli k1 a) (runIKleisli k2 b)
connect (ScopedP (Offer act1 _) k1) (ScopedP (Sel1 act2) k2) = do
  (a, b) <- connect act1 act2
  connect (runIKleisli k1 a) (runIKleisli k2 b)
connect (ScopedP (Offer _ act1) k1) (ScopedP (Sel2 act2) k2) = do
  (a, b) <- connect act1 act2
  connect (runIKleisli k1 a) (runIKleisli k2 b)
connect (ScopedP (LoopSUnbounded act1) k1) (ScopedP (LoopCUnbounded act2) k2) = do
  (a, b) <- go ([], [])
  connect (runIKleisli k1 a) (runIKleisli k2 b)
  where
    go (r1, r2) = do
      (a, b) <- connect act1 act2
      case a of
        Nothing -> pure (r1, b:r2)
        Just a' -> go (a': r1, b:r2)
connect (ScopedP (LoopCUnbounded act1) k1) (ScopedP (LoopSUnbounded act2) k2) = do
  (b, a) <- go ([], [])
  connect (runIKleisli k1 a) (runIKleisli k2 b)
  where
    go (r1, r2) = do
      (b, a) <- connect act1 act2
      case a of
        Nothing -> pure (r1, b:r2)
        Just a' -> go (a': r1, b:r2)

connect _ _ = error "Procol.connect: internal tree error"


connect' ::
  (Dual p1 ~ p2, Dual p2 ~ p1) =>
  PrEff f Session p1 '[End] a ->
  PrEff f Session p2 '[End] b ->
  PrEff f IVoid () () (a, b)
connect' (Value x) (Value y) = pure (x, y)
connect' (ImpureP (Recv) k1) (ImpureP ((Send a)) k2) = connect' (runIKleisli k1 a) (runIKleisli k2 ())
connect' (ImpureP ((Send a)) k1) (ImpureP (Recv) k2) = connect' (runIKleisli k1 ()) (runIKleisli k2 a)
connect' (ScopedP (Sel1 act1) k1) (ScopedP (Offer act2 _) k2) = Ix.do
  (a, b) <- connect' act1 act2
  connect' (runIKleisli k1 a) (runIKleisli k2 b)
connect' (ScopedP (Sel2 act1) k1) (ScopedP (Offer _ act2) k2) = Ix.do
  (a, b) <- connect' act1 act2
  connect' (runIKleisli k1 a) (runIKleisli k2 b)
connect' (ScopedP (Offer act1 _) k1) (ScopedP (Sel1 act2) k2) = Ix.do
  (a, b) <- connect' act1 act2
  connect' (runIKleisli k1 a) (runIKleisli k2 b)
connect' (ScopedP (Offer _ act1) k1) (ScopedP (Sel2 act2) k2) = Ix.do
  (a, b) <- connect' act1 act2
  connect' (runIKleisli k1 a) (runIKleisli k2 b)
connect' (ScopedP (LoopSUnbounded act1) k1) (ScopedP (LoopCUnbounded act2) k2) = Ix.do
  (a, b) <- go ([], [])
  connect' (runIKleisli k1 a) (runIKleisli k2 b)
  where
    go (r1, r2) = Ix.do
      (a, b) <- connect' act1 act2
      case a of
        Nothing -> pure (r1, b:r2)
        Just a' -> go (a': r1, b:r2)
connect' (ScopedP (LoopCUnbounded act1) k1) (ScopedP (LoopSUnbounded act2) k2) = Ix.do
  (a, b) <- go ([], [])
  connect' (runIKleisli k1 a) (runIKleisli k2 b)
  where
    go (r1, r2) = Ix.do
      (a, b) <- connect' act1 act2
      case b of
        Nothing -> pure (a:r1, r2)
        Just b' -> go (a: r1, b':r2)

connect' (Impure cmd k1) k2 = Impure cmd $ iKleisli $ \x -> connect' (runIKleisli k1 x) k2
connect' k1 (Impure cmd k2) = Impure cmd $ iKleisli $ \x -> connect' k1 (runIKleisli  k2 x)
connect' _ _ = error "Procol.connect: internal tree error"
