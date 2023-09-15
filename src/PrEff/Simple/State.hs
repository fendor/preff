module PrEff.Simple.State where

import qualified Control.IxMonad as Ix
import PrEff

data State s x where
  Put :: s -> State s ()
  Get :: State s s

get ::
  Member (State e) f => PrEff f s p p e
get =
  send Get

put ::
  Member (State e) f => e -> PrEff f s p p ()
put s =
  send $ Put s

modify ::
  (Member (State s) effs) =>
  (s -> s) ->
  PrEff effs f ps ps ()
modify f = Ix.do
  s <- get
  put (f s)

runState ::
  (ScopedEffect s) =>
  e ->
  PrEff (State e : f) s ps qs a ->
  PrEff f s ps qs (e, a)
runState initial = interpretStateful initial $ \s -> \case
  Get -> pure (s, s)
  Put newS -> pure (newS, ())

runState' ::
  (ScopedEffect s) =>
  e ->
  PrEff (State e : f) s ps qs a ->
  PrEff f s ps qs (e, a)
runState' s = \case
  Value x -> pure (s, x)
  Impure (OHere op) k -> case op of
    Put s' -> runState' s' (k ())
    Get -> runState' s (k s)
  Impure (OThere op) k ->
    Impure op (\x -> runState' s (k x))
  ImpureP op k ->
    ImpureP op (\x -> runState' s (k x))
  ScopedP op k ->
    ScopedP
      ( weave
          (s, ())
          ( \(s', inner) -> Ix.do
              (x, newS) <- runState' s' inner
              pure (x, newS)
          )
          op
      )
      (\(s', a) -> runState' s' (k a))

execState :: (ScopedEffect f) => a -> PrEff (State a : effs) f p q b -> PrEff effs f p q a
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
