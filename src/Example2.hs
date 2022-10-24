{-# LANGUAGE FlexibleInstances, GADTs, MultiParamTypeClasses,
  RankNTypes, RebindableSyntax, TypeFamilies, TypeInType,
  TypeOperators, UndecidableInstances #-}

module Example2 (res, prog') where

import Control.Monad.Indexed
import Data.TASequence.FastCatQueue
import Prelude hiding ((>>), (>>=))

-- * Indexed free machinery

(>>=)
  :: (IxMonad m)
  => m s1 s2 a -> (a -> m s2 s3 b) -> m s1 s3 b
(>>=) = (>>>=)
(>>)
  :: (IxApplicative m)
  => m s1 s2 a -> m s2 s3 b -> m s1 s3 b
f >> g = imap (const id) f `iap` g

type family Fst x where
  Fst '(a, b) = a
type family Snd x where
  Snd '(a, b) = b

newtype IKleisliTupled m ia ob = IKleisliTupled
  { runIKleisliTupled :: Snd ia -> m (Fst ia) (Fst ob) (Snd ob)
  }

tApp :: (TASequence s, IxMonad m) => s (IKleisliTupled m) x y -> (IKleisliTupled m) x y
tApp fs =
  case tviewl fs of
    TAEmptyL -> IKleisliTupled ireturn
    f :< fs' ->
      IKleisliTupled
        (\a -> runIKleisliTupled f a >>= runIKleisliTupled (tApp fs'))

data Free f s1 s2 a where
  Pure :: a -> Free f s s a
  Impure ::
    f s1 s2 a ->
      FastTCQueue (IKleisliTupled (Free f)) '(s2, a) '(s3, b) ->
        Free f s1 s3 b

instance IxFunctor (Free f) where
  imap f (Pure a) = Pure $ f a
  imap f (Impure a g) = Impure a (g |> IKleisliTupled (Pure . f))
instance IxPointed (Free f) where
  ireturn = Pure
instance IxApplicative (Free f) where
  iap (Pure f) (Pure a) = ireturn $ f a
  iap (Pure f) (Impure a g) = Impure a (g |> IKleisliTupled (Pure . f))
  iap (Impure a f) m = Impure a (f |> IKleisliTupled (`imap` m))
instance IxMonad (Free f) where
  ibind f (Pure a) = f a
  ibind f (Impure a g) = Impure a (g |> IKleisliTupled f)

-- * Example application

data FileStatus
  = FileOpen
  | FileClosed
data File i o a where
  Open :: FilePath -> File 'FileClosed 'FileOpen ()
  Close :: File 'FileOpen 'FileClosed ()
  Read :: File 'FileOpen 'FileOpen String
  Write :: String -> File 'FileOpen 'FileOpen ()

foldFile :: File i o a -> a
foldFile (Open _) = ()
foldFile Close = ()
foldFile Read = "demo"
foldFile (Write _) = ()

data MayFoo
  = YesFoo
  | NoFoo
data Foo i o a where
  Foo :: Foo 'NoFoo 'YesFoo ()

data MayBar
  = YesBar
  | NoBar
data Bar i o a where
  Bar :: Bar 'YesBar 'NoBar ()

-- * Coproduct of indexed functors

infixr 5 `SumP`
data SumP f1 f2 t1 t2 x where
  LP :: f1 sl1 sl2 x -> SumP f1 f2 '(sl1, sr) '(sl2, sr) x
  RP :: f2 sr1 sr2 x -> SumP f1 f2 '(sl, sr1) '(sl, sr2) x

newtype VoidFunctor is os a = VoidFunctor (VoidFunctor is os a)
absurd :: VoidFunctor is os a -> b
absurd a = a `seq` spin a where
   spin (VoidFunctor b) = spin b

extract :: Free VoidFunctor '() '() a -> a
extract (Pure a) = a
extract (Impure f _) = absurd f

runPure
  :: (forall j p b. f j p b -> b)
  -> Free (f `SumP` fs) '(i, is) '(o, os) a
  -> Free fs is os a
runPure _ (Pure a) = Pure a
runPure f (Impure (RP cmd) q) = Impure cmd (tsingleton k)
  where k = IKleisliTupled $ \a -> runPure f $ runIKleisliTupled (tApp q) a
runPure f (Impure (LP cmd) q) = runPure f $ runIKleisliTupled (tApp q) (f cmd)

-- * Injection

class Inject l b where
  inj :: forall a. l a -> b a

instance Inject (f i o) (f i o) where
  inj = id

instance {-# OVERLAPPING #-}
  (is ~ '(il, s), os ~ '(ol, s)) =>
  Inject (fl il ol) (SumP fl fr is os) where
  inj = LP

instance (Inject (f i' o') (fr is' os'), is ~ '(s, is'), os ~ '(s, os')) =>
         Inject (f i' o') (SumP fl fr is os) where
  inj = RP . inj

send
  :: Inject (t i o) (f is os)
  => t i o b -> Free f is os b
send t = Impure (inj t) (tsingleton (IKleisliTupled Pure))

-- * In use

prog = do
  send (Open "/tmp/foo.txt")
  x <- send Read
  send Foo
  send (Write x)
  send Bar
  send Close
  ireturn x

prog' ::
  Free
    (File `SumP` Foo `SumP` Bar `SumP` VoidFunctor)
    '( 'FileClosed, '( 'NoFoo, '( 'YesBar, '())))
    '( 'FileClosed, '( 'YesFoo, '( 'NoBar, '())))
    String
prog' = prog

res :: String
res = extract . runPure (\Bar -> ()) . runPure (\Foo -> ()) . runPure foldFile $ prog
