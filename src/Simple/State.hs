{-# LANGUAGE QualifiedDo #-}
module Simple.State where

import Utils
import qualified Utils as I
import Prelude hiding (Monad (..))
import Unsafe.Coerce
import Data.Proxy
import GHC.TypeLits
import Data.Typeable

data StateS s p q x where
  PutS :: s -> StateS s () () ()
  GetS :: StateS s () () s
  deriving (Typeable)

data StateG s m p p' q' q x x' where
  ModifyG :: (s -> s) -> m (():sr1) (():sr2) x -> StateG s m (():sr1) (():sr1) ((): sr2) (():sr1) x x

getS :: forall s effs (ind :: Natural) g ps .
  (FindEff (StateS s) effs ~ ind, KnownNat ind) =>
  IProg effs g ps ps s
getS = Impure (inj (Proxy :: Proxy ind) GetS) emptyCont

putS :: forall s effs ind g ps .
  ( FindEff (StateS s) effs ~ ind
  , KnownNat ind
  ) =>
  s -> IProg effs g ps ps ()
putS s = Impure (inj (Proxy :: Proxy ind) $ PutS s) emptyCont

modifyG ::
  (s -> s) ->
  IProg f (StateG s) (():ps) (():ps) a ->
  IProg f (StateG s) (():ps) (():ps) a
modifyG f prog = Scope (ModifyG f prog) undefined -- emptyCont

runStateG :: forall p q s effs ps qs a .
  s ->
  IProg (StateS s: effs) (StateG s) (p:ps) (q:qs) a ->
  IProg effs IVoid ps qs (s, a)
runStateG s (Pure a) = I.return (s, a)
runStateG s (Impure (OHere GetS) k) = runStateG s (runIKleisliTupled k s)
runStateG _s (Impure (OHere (PutS s')) k) = runStateG s' (runIKleisliTupled k ())
runStateG s (Impure (OThere cmd) k) = Impure cmd $ IKleisliTupled (runStateG s . runIKleisliTupled k)
runStateG s (Scope (ModifyG f prog) k) = I.do
  (_s, x) <- runStateG (f s) prog -- :: IProg effs IVoid ps sr2 (s, x)
  runStateG s (unsafeCoerce runIKleisliTupled k x)
 where

runState :: forall p q s effs ps qs a .
  s ->
  IProg (StateS s:effs) IVoid (p:ps) (q:qs) a ->
  IProg effs IVoid ps qs (s, a)
runState s (Pure a) = I.return (s, a)
runState s (Impure (OHere GetS) k) = runState s (runIKleisliTupled k s)
runState _s (Impure (OHere (PutS s')) k) = runState s' (runIKleisliTupled k ())
runState s (Impure (OThere cmd) k) = Impure cmd $ IKleisliTupled (runState s . runIKleisliTupled k)
runState _ (Scope _ _) = error "Impossible, Scope node must never be created"

stateExample ::
  (FindEff (StateS Int) effs ~ ind, KnownNat ind) =>
  IProg effs g ps ps String
stateExample = I.do
  i <- getS @Int
  putS (i + i)
  I.return $ show i

-- stateWithLocal ::
--   ( SMember (StateS Int) effs ps ps
--   , g ~ StateG Int
--   ) =>
--   IProg effs g ps ps String
-- stateWithLocal = I.do
--   n <- getS @Int
--   x <- modifyG (+ n) stateExample
--   return $ x ++ ", initial: " ++ show n

-- -- ambiguityExample :: forall effs ps qs g . SMember (StateS Int) effs ps qs => IProg effs g ps qs Int

-- ambiguityExample ::
--   (SMember (StateS Int) effs ps ps) =>
--   IProg effs g ps ps Int
-- ambiguityExample = I.do
--   i <- getS
--   i2 <- getS
--   putS (i + i2)
--   I.return $ i + i2

-- moreExamples ::
--   ( SMember (StateS Int) effs ps ps
--   , SMember (StateS String) effs ps ps
--   ) =>
--   IProg effs g ps ps Int
-- moreExamples = I.do
--   i <- getS -- :: forall js . IProg effs g ps js Int
--   i2 <- getS -- :: forall js . IProg effs g js qs Int
--   (m :: String) <- getS
--   putS (m ++ reverse m)
--   _ <- ambiguityExample
--   I.return $ i + i2

-- -- runner :: IProg '[IIdentity] IVoid '[()] '[()] (Int, String)
-- runner = runState @() @() "mama" $ runStateG @() @() (5 :: Int) moreExamples
