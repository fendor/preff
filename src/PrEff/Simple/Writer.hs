{-# LANGUAGE QualifiedDo #-}

module PrEff.Simple.Writer where
import PrEff
import qualified Control.IxMonad as Ix

data Writer w a where
  Tell :: w -> Writer w ()

tell :: Member (Writer s) effs => s -> PrEff effs f p p ()
tell = send . Tell

runWriter :: (ScopedEffect s, Monoid w) =>
  PrEff (Writer w : effs) s p q a ->
  PrEff effs s p q (a, w)
runWriter (Value a) = Ix.return (a, mempty)
runWriter (Impure (OHere (Tell w)) k) = fmap (\(a, w') -> (a, w <> w')) $ runWriter (runIKleisliTupled k ())
runWriter (Impure (OThere cmd) k) = Impure cmd $ hdl runWriter k
runWriter (ImpureP cmd k) = ImpureP cmd $ hdl runWriter k
runWriter (ScopedP op k) =
  ScopedP
    (mapS (mempty,()) ntW op)
    (IKleisliTupled $ \(s, x) -> fmap (\(a, w) -> (a, s <> w)) . runWriter $ runIKleisliTupled k x)

ntW :: (ScopedEffect s, Monoid w) => HandlerS ((,) w) (PrEff (Writer w :effs) s) (PrEff effs s)
ntW = \(w, m) -> fmap (\(a, w') -> (w <> w', a)) $ runWriter m
