{-# LANGUAGE QualifiedDo #-}

module Simple.State where

import Data.Typeable
import Utils
import qualified Utils as I

data StateS s x where
  PutS :: s -> StateS s ()
  GetS :: StateS s s
  deriving (Typeable)

data StateP s p q x where
  PutP :: s -> StateP s () () ()
  GetP :: StateP s () () s

data instance ScopeT (StateP s) m p p' q' q x x' where
  ModifyP ::
    (s -> s) ->
    m () () x ->
    ScopeT (StateP s) m () () () () x x

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
  (Value a) -> I.return (s, a)
  (Impure op k) -> Impure op $ IKleisliTupled $ \x -> runStateP s (runIKleisliTupled k x)
  (ImpureP (PutP s') k) -> runStateP s' $ runIKleisliTupled k ()
  (ImpureP GetP k) -> runStateP s $ runIKleisliTupled k s
  (ScopedP (ModifyP f act) k) -> I.do
    (s', v) <- runStateP (f s) act
    runStateP s' $ runIKleisliTupled k v

getS ::
  (Member (StateS s) effs) =>
  MiniEff effs f ps ps s
getS = send GetS

putS ::
  ( Member (StateS s) effs
  ) =>
  s ->
  MiniEff effs f ps ps ()
putS s = send $ PutS s

runState :: ScopedEffect f =>
  s ->
  MiniEff (StateS s : effs) f ps qs a ->
  MiniEff effs f ps qs (s, a)
runState s (Value a) = I.return (s, a)
runState s (Impure (OHere GetS) k) = runState s (runIKleisliTupled k s)
runState _s (Impure (OHere (PutS s')) k) = runState s' (runIKleisliTupled k ())
runState s (Impure (OThere cmd) k) = Impure cmd $ IKleisliTupled (runState s . runIKleisliTupled k)
runState s (ImpureP cmd k) = ImpureP cmd (IKleisliTupled $ runState s . runIKleisliTupled k)
runState s (ScopedP op k) =
  ScopedP
    (weave (s, ()) (uncurry runState) op)
    (IKleisliTupled $ \(s', a) -> runState s' $ runIKleisliTupled k a)

stateExample ::
  (Member (StateS Int) effs) =>
  MiniEff effs f ps ps String
stateExample = I.do
  i <- getS @Int
  putS (i + i)
  I.return $ show i

ambiguityExample ::
  (Member (StateS Int) effs) =>
  MiniEff effs f ps ps Int
ambiguityExample = I.do
  i <- getS
  i2 <- getS
  putS (i + i2)
  I.return $ i + i2

moreExamples ::
  ( Member (StateS Int) effs
  , Member (StateS String) effs
  ) =>
  MiniEff effs f ps ps Int
moreExamples = I.do
  i <- getS -- :: forall js . MiniEff effs g ps js Int
  i2 <- getS -- :: forall js . MiniEff effs g js qs Int
  (m :: String) <- getS
  putS (m ++ reverse m)
  _ <- ambiguityExample
  I.return $ i + i2

-- -- runner :: MiniEff '[IIdentity] IVoid '[()] '[()] (Int, String)
-- runner = runState @() @() "mama" $ runStateG @() @() (5 :: Int) moreExamples
