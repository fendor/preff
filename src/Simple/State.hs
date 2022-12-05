{-# LANGUAGE QualifiedDo #-}

module Simple.State where

import Data.Typeable
import Utils
import qualified Utils as I

data StateS s x where
  PutS :: s -> StateS s ()
  GetS :: StateS s s
  deriving (Typeable)

getS ::
  (SMember (StateS s) effs) =>
  MiniEff effs f g ps ps s
getS = Impure (inj GetS) emptyCont

putS ::
  ( SMember (StateS s) effs
  ) =>
  s ->
  MiniEff effs f g ps ps ()
putS s = Impure (inj $ PutS s) emptyCont

runState ::
  s ->
  MiniEff (StateS s : effs) IIdentity IVoid ps qs a ->
  MiniEff effs IIdentity IVoid ps qs (s, a)
runState s (Value a) = I.return (s, a)
runState s (Impure (OHere GetS) k) = runState s (runIKleisliTupled k s)
runState _s (Impure (OHere (PutS s')) k) = runState s' (runIKleisliTupled k ())
runState s (Impure (OThere cmd) k) = Impure cmd $ IKleisliTupled (runState s . runIKleisliTupled k)
runState e (ImpureT cmd k) = ImpureT cmd (IKleisliTupled $ runState e . runIKleisliTupled k)
runState _ (ScopeT _ _) = error "Impossible, Scope node must never be created"

stateExample ::
  (SMember (StateS Int) effs) =>
  MiniEff effs f g ps ps String
stateExample = I.do
  i <- getS @Int
  putS (i + i)
  I.return $ show i

-- stateWithLocal ::
--   ( SMember (StateS Int) effs ps ps
--   , g ~ StateG Int
--   ) =>
--   MiniEff effs g ps ps String
-- stateWithLocal = I.do
--   n <- getS @Int
--   x <- modifyG (+ n) stateExample
--   return $ x ++ ", initial: " ++ show n

-- -- ambiguityExample :: forall effs ps qs g . SMember (StateS Int) effs ps qs => MiniEff effs g ps qs Int

ambiguityExample ::
  (SMember (StateS Int) effs) =>
  MiniEff effs f g ps ps Int
ambiguityExample = I.do
  i <- getS
  i2 <- getS
  putS (i + i2)
  I.return $ i + i2

moreExamples ::
  ( SMember (StateS Int) effs
  , SMember (StateS String) effs
  ) =>
  MiniEff effs f g ps ps Int
moreExamples = I.do
  i <- getS -- :: forall js . MiniEff effs g ps js Int
  i2 <- getS -- :: forall js . MiniEff effs g js qs Int
  (m :: String) <- getS
  putS (m ++ reverse m)
  _ <- ambiguityExample
  I.return $ i + i2

-- -- runner :: MiniEff '[IIdentity] IVoid '[()] '[()] (Int, String)
-- runner = runState @() @() "mama" $ runStateG @() @() (5 :: Int) moreExamples
