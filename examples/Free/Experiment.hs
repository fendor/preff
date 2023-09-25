{-# LANGUAGE TemplateHaskell #-}

module Free.Experiment where

import qualified Control.IxMonad as Ix
import Control.Monad.Codensity
import Control.Monad.Free
import Control.Monad.Free.Church
import qualified Control.Monad.Free.Church as Church
import Data.Kind (Type)

-- getOut :: Sing (SetAt n p xs) -> Sing p
-- getOut m = undefined

data TreeF a = NodeF a a
  deriving (Show, Eq, Ord, Functor, Traversable, Foldable)

type Tree a = Free TreeF a
type Tree' a = Codensity (Free TreeF) a

data StateF e a
  = Get (e -> a)
  | Put !e a
  deriving (Functor)

type State e = Codensity (Free (StateF e))

{-# INLINEABLE get #-}
{-# INLINEABLE put #-}

{-# INLINEABLE getC #-}
{-# INLINEABLE putC #-}

{-# INLINEABLE getF #-}
{-# INLINEABLE putF #-}

{-# INLINEABLE getM #-}
{-# INLINEABLE putM #-}

{-# INLINEABLE increment #-}
{-# INLINEABLE incrementC #-}
{-# INLINEABLE incrementF #-}
{-# INLINEABLE incrementM #-}
{-# INLINEABLE incrementFast #-}

newtype ICodensity m j k a = ICodensity
  { runICodensity :: forall b i. (a -> m i j b) -> m i k b
  }

-- newtype GCodensity m f a = GCodensity
--   { runGCodensity :: forall c g . (a -> m g c) -> m (f <> g) c
--   }

instance Ix.IFunctor (ICodensity m) where
  imap f (ICodensity run) = ICodensity $ \k ->
    run (\a -> k (f a))

instance Ix.IApplicative (ICodensity m) where
  pure :: a -> ICodensity m k k a
  pure a = ICodensity $ \k -> k a

  (<*>) :: ICodensity m i j (a -> b) -> ICodensity m j r a -> ICodensity m i r b
  f <*> g =
    ICodensity $ \bfr ->
      runICodensity g $ \x -> runICodensity f $ \ab -> bfr (ab x)

exp :: Ix.IMonad m => forall b i . (a -> m j k b) -> m i k b
exp = (Ix.>>=) (undefined :: m j k a)

-- instance Ix.IMonad (ICodensity m) where
--   (>>=) ::
--     ICodensity m j k a -> (a -> ICodensity m k r b) -> ICodensity m j r b
--   m >>= k = ICodensity (\(c :: forall c i . (b -> m i j c)) ->
--     runICodensity (runICodensity m $ \a -> k a) c)

get :: Free (StateF e) e
get = Free (Get (\x -> Pure x))

put :: e -> Free (StateF e) ()
put e = Free (Put e (Pure ()))

putC :: e -> State e ()
putC e = Codensity (put e >>=)

getC :: State e e
getC = Codensity (get >>=)

getF :: F (StateF e) e
getF = toF get

putF :: e -> F (StateF e) ()
putF e = toF (put e)

getM :: (MonadFree (StateF e) m) => m e
getM = wrap (Get (\x -> pure x))

putM :: (MonadFree (StateF e) m) => e -> m ()
putM e = wrap (Put e (pure ()))

-- ----------------------------------------------------------------------------
-- Experiment for cross module optimisation checks
-- ----------------------------------------------------------------------------

freeMonadExp :: Integer -> (Integer, Integer)
freeMonadExp start = runState 0 (Church.improve (prog start >>= prog >>= prog))
 where
  prog s =
    incrementM s >>= incrementM >>= incrementM

-- ----------------------------------------------------------------------------
-- Runners
-- ----------------------------------------------------------------------------

runStateC :: e -> Codensity (Free (StateF e)) a -> (a, e)
runStateC i prog = runState i (lowerCodensity prog)

runState :: e -> Free (StateF e) a -> (a, e)
runState s = \case
  Pure a -> (a, s)
  Free op -> case op of
    Get k -> runState s (k s)
    Put e k -> runState e k

runStateChurch :: e -> F (StateF e) a -> (a, e)
runStateChurch start op =
  ( runF
      op
      (\a s -> (a, s))
      ( \cases
          (Get k) s -> k s s
          (Put e k) _s -> k e
      )
  )
    start

-- ----------------------------------------------------------------------------
-- Increment code
-- ----------------------------------------------------------------------------

incrementC :: Integer -> State Integer Integer
incrementC n = do
  if n <= 0
    then getC
    else do
      x <- getC
      putC (x + 1)
      incrementC (n - 1)

incrementF :: Integer -> F (StateF Integer) Integer
incrementF n = do
  if n <= 0
    then getF
    else do
      x <- getF
      putF (x + 1)
      incrementF (n - 1)

increment :: Integer -> Free (StateF Integer) Integer
increment n = do
  if n <= 0
    then get
    else do
      x <- get
      put (x + 1)
      increment (n - 1)

incrementM :: (MonadFree (StateF Integer) m) => Integer -> m Integer
incrementM n = do
  if n <= 0
    then getM
    else do
      x <- getM
      putM (x + 1)
      incrementM (n - 1)

incrementFast :: Integer -> Integer -> (Integer, Integer)
incrementFast n !x = do
  if n <= 0
    then (x, x)
    else do
      incrementFast (n - 1) (x + 1)
