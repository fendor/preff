module PrEff.Codensity.State where

import qualified Control.IxMonad as Ix
import PrEff

data State s x where
  Put :: !s -> State s ()
  Get :: State s s

get ::
  Member (State e) f => Eff f s p p e
get =
  wrap $ send Get

put ::
  Member (State e) f => e -> Eff f s p p ()
put s =
  wrap . send $ Put s

modify ::
  (Member (State s) effs) =>
  (s -> s) ->
  Eff effs f ps ps ()
modify f = Ix.do
  s <- get
  put (f s)

runState ::
  (ScopedEffect s) =>
  e ->
  PrEff (State e : f) s ps qs a ->
  PrEff f s ps qs (e, a)
runState !initial = interpretStateful initial $ \ !s -> \case
  Get -> pure (s, s)
  Put newS -> pure (newS, ())

execState :: (ScopedEffect f) => a -> PrEff (State a : effs) f p q b -> PrEff effs f p q a
execState s = Ix.imap fst . runState s

stateExample ::
  (Member (State Int) effs) =>
  Eff effs f ps ps String
stateExample = Ix.do
  i <- get @Int
  put (i + i)
  pure $ show i

ambiguityExample ::
  (Member (State Int) effs) =>
  Eff effs f ps ps Int
ambiguityExample = Ix.do
  i <- get
  i2 <- get
  put (i + i2)
  pure $ i + i2

moreExamples ::
  ( Member (State Int) effs
  , Member (State String) effs
  ) =>
  Eff effs f ps ps Int
moreExamples = Ix.do
  i <- get -- :: forall js . PrEff effs g ps js Int
  i2 <- get -- :: forall js . PrEff effs g js qs Int
  (m :: String) <- get
  put (m ++ reverse m)
  _ <- ambiguityExample
  pure $ i + i2

-- -- runner :: PrEff '[IIdentity] IVoid '[()] '[()] (Int, String)
-- runner = runState @() @() "mama" $ runStateG @() @() (5 :: Int) moreExamples
