module PrEff.Simple.State where

import Data.Typeable
import PrEff
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

putP :: s -> PrEff eff (StateP s) () () ()
putP s = sendP $ PutP s

getP :: PrEff eff (StateP a) () () a
getP = sendP $ GetP

runStateP :: s ->
  PrEff effs (StateP s) () () a ->
  PrEff effs IVoid () () (s, a)
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
  PrEff effs f ps ps s
get = send Get

put ::
  ( Member (State s) effs
  ) =>
  s ->
  PrEff effs f ps ps ()
put s = send $ Put s

modify :: Member (State s) effs =>
  (s -> s) ->
  PrEff effs f ps ps ()
modify f = Ix.do
  s <- get
  put (f s)

runState :: ScopedEffect s =>
  e ->
  PrEff (State e : f) s ps qs a ->
  PrEff f s ps qs (e, a)
runState initial = interpretStateful initial $ \s -> \case
  Get -> pure (s, s)
  Put newS -> pure (newS, ())

execState :: ScopedEffect f => a -> PrEff (State a : effs) f p q b -> PrEff effs f p q a
execState s = Ix.imap fst . runState s

stateExample ::
  (Member (State Int) effs) =>
  PrEff effs f ps ps String
stateExample = Ix.do
  i <- get @Int
  put (i + i)
  Ix.return $ show i

ambiguityExample ::
  (Member (State Int) effs) =>
  PrEff effs f ps ps Int
ambiguityExample = Ix.do
  i <- get
  i2 <- get
  put (i + i2)
  Ix.return $ i + i2

moreExamples ::
  ( Member (State Int) effs
  , Member (State String) effs
  ) =>
  PrEff effs f ps ps Int
moreExamples = Ix.do
  i <- get -- :: forall js . PrEff effs g ps js Int
  i2 <- get -- :: forall js . PrEff effs g js qs Int
  (m :: String) <- get
  put (m ++ reverse m)
  _ <- ambiguityExample
  Ix.return $ i + i2

-- -- runner :: PrEff '[IIdentity] IVoid '[()] '[()] (Int, String)
-- runner = runState @() @() "mama" $ runStateG @() @() (5 :: Int) moreExamples
