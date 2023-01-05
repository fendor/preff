{-# LANGUAGE QualifiedDo #-}

module MiniEff.Simple.State where

import Data.Typeable
import MiniEff
import qualified Control.IxMonad as Ix

data State s x where
  Put :: !s -> State s ()
  Get :: State s s
  deriving (Typeable)

data StateP s p q x where
  PutP :: !s -> StateP s () () ()
  GetP :: StateP s () () s

data instance ScopeE (StateP s) m p p' q' q x x' where
  ModifyP ::
    (s -> s) ->
    m () () x ->
    ScopeE (StateP s) m () () () () x x

instance ScopedEffect (StateP s) where
  mapS ctx nt (ModifyP f act) =
    ModifyP f (nt $ act <$ ctx)

putP :: s -> MiniEff eff (StateP s) () () ()
putP s = sendP $ PutP s

getP :: MiniEff eff (StateP a) () () a
getP = sendP $ GetP

runStateP :: s ->
  MiniEff effs (StateP s) () () a ->
  MiniEff effs IVoid () () (s, a)
runStateP s = \case
  (Value a) -> Ix.return (s, a)
  (Impure op k) -> Impure op $ IKleisliTupled $ \x -> runStateP s (runIKleisliTupled k x)
  (ImpureP (PutP s') k) -> runStateP s' $ runIKleisliTupled k ()
  (ImpureP GetP k) -> runStateP s $ runIKleisliTupled k s
  (ScopedP (ModifyP f act) k) -> Ix.do
    (s', v) <- runStateP (f s) act
    runStateP s' $ runIKleisliTupled k v

get ::
  (Member (State s) effs) =>
  MiniEff effs f ps ps s
get = send Get

put ::
  ( Member (State s) effs
  ) =>
  s ->
  MiniEff effs f ps ps ()
put s = send $ Put s

modify :: Member (State s) effs =>
  (s -> s) ->
  MiniEff effs f ps ps ()
modify f = Ix.do
  s <- get
  put (f s)

runState :: ScopedEffect f =>
  s ->
  MiniEff (State s : effs) f ps qs a ->
  MiniEff effs f ps qs (s, a)
runState s (Value a) = Ix.return (s, a)
runState s (Impure (OHere Get) k) = runState s (runIKleisliTupled k s)
runState _s (Impure (OHere (Put s')) k) = runState s' (runIKleisliTupled k ())
runState s (Impure (OThere cmd) k) = Impure cmd $ IKleisliTupled (runState s . runIKleisliTupled k)
runState s (ImpureP cmd k) = ImpureP cmd (IKleisliTupled $ runState s . runIKleisliTupled k)
runState s (ScopedP op k) =
  ScopedP
    (weave (s, ()) (uncurry runState) op)
    (IKleisliTupled $ \(s', a) -> runState s' $ runIKleisliTupled k a)

execState :: ScopedEffect f => a -> MiniEff (State a : effs) f p q b -> MiniEff effs f p q a
execState s = Ix.imap fst . runState s

stateExample ::
  (Member (State Int) effs) =>
  MiniEff effs f ps ps String
stateExample = Ix.do
  i <- get @Int
  put (i + i)
  Ix.return $ show i

ambiguityExample ::
  (Member (State Int) effs) =>
  MiniEff effs f ps ps Int
ambiguityExample = Ix.do
  i <- get
  i2 <- get
  put (i + i2)
  Ix.return $ i + i2

moreExamples ::
  ( Member (State Int) effs
  , Member (State String) effs
  ) =>
  MiniEff effs f ps ps Int
moreExamples = Ix.do
  i <- get -- :: forall js . MiniEff effs g ps js Int
  i2 <- get -- :: forall js . MiniEff effs g js qs Int
  (m :: String) <- get
  put (m ++ reverse m)
  _ <- ambiguityExample
  Ix.return $ i + i2

-- -- runner :: MiniEff '[IIdentity] IVoid '[()] '[()] (Int, String)
-- runner = runState @() @() "mama" $ runStateG @() @() (5 :: Int) moreExamples
