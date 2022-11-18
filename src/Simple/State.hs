{-# LANGUAGE QualifiedDo #-}
module Simple.State where

import Utils
import qualified Utils as I
import Prelude hiding (Monad (..))

data StateS s p q x where
  PutS :: s -> StateS s () () ()
  GetS :: StateS s () () s

data StateG s m p p' q' q x x' where
  LocalG :: (s -> s) -> m p' q' x -> StateG s m p p' q' q x x

getS :: forall s g effs ps qs . SMember (StateS s) effs ps qs => IProg effs g ps qs s
getS = Impure (inj GetS) emptyCont

putS ::
  SMember (StateS s) effs ps qs =>
  s -> IProg effs g ps qs ()
putS s = Impure (inj $ PutS s) emptyCont

localG :: (s -> s) -> IProg f (StateG s) q r a -> IProg f (StateG s) p r a
localG f prog = Scope (LocalG f prog) emptyCont

runStateS :: s -> IProg '[StateS s] (StateG s) p q a -> (s, a)
runStateS s (Pure a) = (s, a)
runStateS s (Impure (OHere GetS) k) = runStateS s (runIKleisliTupled k s)
runStateS _s (Impure (OHere (PutS s')) k) = runStateS s' (runIKleisliTupled k ())
runStateS _s (Impure (OThere _) _k) = error "Inaccessible"
runStateS s (Scope (LocalG f prog) k) = runStateS s (runIKleisliTupled k x)
 where
  (_, x) = runStateS (f s) prog

-- runState ::
--   s ->
--   IProg (StateS s:effs) IVoid (():ps) (():qs) a ->
--   IProg (StateS s:effs) IVoid (():ps) (():qs) (s, a)
-- runState s (Pure a) = I.return (s, a)
-- runState s (Impure (OHere GetS) k) = runState s (runIKleisliTupled k s)
-- runState _s (Impure (OHere (PutS s')) k) = runState s' (runIKleisliTupled k ())
-- runState s (Impure (OThere _) _k) = error "Inaccessible"
-- runState _ (Scope _ _) = error "Impossible, Scope node must never be created"

-- stateExample :: SMember (StateS Int) () () effs ps qs => IProg effs g ps qs String
-- stateExample = I.do
--   i <- getS @Int
--   putS (i + i)
--   I.return $ show i

-- stateWithLocal :: IProg '[StateS Int] (StateG Int) '[()] '[()] String
-- stateWithLocal = do
--   n <- getS @Int
--   x <- localG (+ n) stateExample
--   return $ x ++ ", initial: " ++ show n

ambiguityExample :: SMember (StateS Int) effs ps qs => IProg effs g ps qs Int
ambiguityExample = I.do
  i <- getS @Int
  i2 <- getS @Int
  I.return $ i
