{-# LANGUAGE QualifiedDo #-}
module Simple.State where

import Utils
import qualified Utils as I
import Prelude hiding (Monad (..))
import Unsafe.Coerce

data StateS s p q x where
  PutS :: s -> StateS s () () ()
  GetS :: StateS s () () s

data StateG s m p p' q' q x x' where
  ModifyG :: (s -> s) -> m p' q' x -> StateG s m p' p' q' q' x x

getS :: forall s g effs ps . SMember (StateS s) effs ps ps => IProg effs g ps ps s
getS = Impure (inj GetS) emptyCont

putS ::
  SMember (StateS s) effs ps ps =>
  s -> IProg effs g ps ps ()
putS s = Impure (inj $ PutS s) emptyCont

modifyG :: (s -> s) -> IProg f (StateG s) p r a -> IProg f (StateG s) p r a
modifyG f prog = Scope (ModifyG f prog) emptyCont

runStateS :: forall p q s effs ps qs a .
  s ->
  IProg (StateS s: effs) (StateG s) (p:ps) (q:qs) a ->
  IProg effs IVoid ps qs (s, a)
runStateS s (Pure a) = I.return (s, a)
runStateS s (Impure (OHere GetS) k) = runStateS s (unsafeCoerce runIKleisliTupled k s)
runStateS _s (Impure (OHere (PutS s')) k) = runStateS s' (unsafeCoerce runIKleisliTupled k ())
runStateS s (Impure (OThere cmd) k) = Impure cmd $ IKleisliTupled (runStateS s . runIKleisliTupled k)
runStateS s (Scope (ModifyG f prog) k) = I.do
  (_, x) <- runStateS (f s) $ unsafeCoerce prog
  runStateS s (unsafeCoerce runIKleisliTupled k x)
 where

runState :: forall p q s effs ps qs a .
  s ->
  IProg (StateS s:effs) IVoid (p:ps) (q:qs) a ->
  IProg effs IVoid ps qs (s, a)
runState s (Pure a) = I.return (s, a)
runState s (Impure (OHere GetS) k) = runState s (unsafeCoerce runIKleisliTupled k s)
runState _s (Impure (OHere (PutS s')) k) = runState s' (unsafeCoerce runIKleisliTupled k ())
runState s (Impure (OThere cmd) k) = Impure cmd $ IKleisliTupled (runState s . runIKleisliTupled k)
runState _ (Scope _ _) = error "Impossible, Scope node must never be created"

stateExample ::
  SMember (StateS Int) effs ps ps =>
  IProg effs g ps ps String
stateExample = I.do
  i <- getS @Int
  putS (i + i)
  I.return $ show i

stateWithLocal ::
  ( SMember (StateS Int) effs ps ps
  , g ~ StateG Int
  ) =>
  IProg effs g ps ps String
stateWithLocal = I.do
  n <- getS @Int
  x <- modifyG (+ n) stateExample
  return $ x ++ ", initial: " ++ show n

-- ambiguityExample :: forall effs ps qs g . SMember (StateS Int) effs ps qs => IProg effs g ps qs Int

ambiguityExample ::
  (SMember (StateS Int) effs ps ps) =>
  IProg effs g ps ps Int
ambiguityExample = I.do
  i <- getS -- :: forall js . IProg effs g ps js Int
  i2 <- getS -- :: forall js . IProg effs g js qs Int
  putS (i + i2)
  I.return $ i + i2

moreExamples ::
  ( SMember (StateS Int) effs ps ps
  , SMember (StateS String) effs ps ps
  ) =>
  IProg effs g ps ps Int
moreExamples = I.do
  i <- getS -- :: forall js . IProg effs g ps js Int
  i2 <- getS -- :: forall js . IProg effs g js qs Int
  (m :: String) <- getS
  putS (m ++ reverse m)
  _ <- ambiguityExample
  I.return $ i + i2

-- runner :: IProg '[IIdentity] IVoid '[()] '[()] (Int, String)
runner = runState @() @() "mama" $ runStateS @() @() (5 :: Int) moreExamples