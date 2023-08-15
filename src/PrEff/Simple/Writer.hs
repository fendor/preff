{-# LANGUAGE QualifiedDo #-}

module PrEff.Simple.Writer where
import PrEff

data Writer w a where
  Tell :: w -> Writer w ()

tell :: Member (Writer s) effs => s -> PrEff effs f p p ()
tell = send . Tell

runWriter :: forall w a effs s p q .
  (ScopedEffect s, Monoid w) =>
  PrEff (Writer w : effs) s p q a ->
  PrEff effs s p q (w, a)
runWriter = interpretStateful mempty $ \s -> \case
  Tell w -> pure (s <> w, ())

writerExample :: Member (Writer [Int]) f => PrEff f s p p ()
writerExample = do
  tell @[Int] [1]
  tell @[Int] [2]
  tell @[Int] [3, 4, 5]
