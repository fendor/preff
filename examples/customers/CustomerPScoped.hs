module CustomerPScoped where

import qualified Control.IxMonad as Ix
import Data.Map
import qualified Data.Map as Map
import Data.Proxy
import qualified Data.Text as T
import GHC.TypeLits
import PrEff
import PrEff.Simple.State
import PrEff.Simple.Writer
import System.Directory (doesFileExist)
import System.FilePath
import Utils

data Store inp
data Empty

data CustomerStore p q a where
  ReadStore :: (KnownSymbol inp) => proxy inp -> CustomerStore (Store inp) (Store inp) [Customer]
  WriteStore :: (KnownSymbol out) => proxy out -> [Customer] -> CustomerStore p (Store out) ()

data instance ScopeE CustomerStore m p p' q' q x' x where
  WithStore ::
    (KnownSymbol inp) =>
    proxy inp ->
    m (Store inp) q' () ->
    ScopeE CustomerStore m p (Store inp) q' p () ()

readStore :: (KnownSymbol inp) => proxy inp -> PrEff eff CustomerStore (Store inp) (Store inp) [Customer]
readStore p = sendP (ReadStore p)

writeStore :: (KnownSymbol out) => proxy out -> [Customer] -> PrEff eff CustomerStore p (Store out) ()
writeStore p c = sendP (WriteStore p c)

withStore :: (KnownSymbol inp) => proxy inp -> PrEff eff CustomerStore (Store inp) (Store out) () -> PrEff eff CustomerStore p p ()
withStore i m = sendScoped (WithStore i m)

runCustomerStoreIO ::
  (Member (Embed IO) f) =>
  PrEff f CustomerStore p q a ->
  PrEff f IVoid () () a
runCustomerStoreIO =
  interpretScoped
    ( \case
        ReadStore (p :: proxy inp) -> do
          let fp = symbolVal p
          embed $ readCustomersIO fp
        WriteStore (p :: proxy out) cs -> do
          let fp = symbolVal p
          embed $ writeCustomersIO fp cs
    )
    ( \k runner -> \case
        WithStore p m -> do
          let fp = symbolVal p
          embed (customersExistIO fp) >>= \case
            False ->
              runner $ runIKleisliTupled k ()
            True -> do
              _a <- runner m
              runner $ runIKleisliTupled k ()
    )

runCustomerStoreViaState ::
  (Member (State (Map FilePath [Customer])) f) =>
  PrEff f CustomerStore p q a ->
  PrEff f IVoid () () a
runCustomerStoreViaState =
  interpretScoped
    ( \case
        ReadStore (p :: proxy inp) -> do
          let fp = symbolVal p
          s <- get
          pure $ s ! fp
        WriteStore (p :: proxy out) cs -> do
          let fp = symbolVal p
          s <- get
          put (insert fp cs s)
    )
    ( \k runner -> \case
        WithStore p m -> do
          let fp = symbolVal p
          s <- get @(Map FilePath [Customer])
          case Map.lookup fp s of
            Nothing ->
              runner $ runIKleisliTupled k ()
            Just _ -> do
              _a <- runner m
              runner $ runIKleisliTupled k ()
    )

processCustomers ::
  (Member CustomerService f, KnownSymbol inp, KnownSymbol out) =>
  Proxy inp ->
  Proxy out ->
  PrEff f CustomerStore (Store inp) (Store out) ()
processCustomers inp out = Ix.do
  customers <- readStore inp
  newCustomers <- process customers
  writeStore out newCustomers

invocationExample ::
  (Members [Writer [String], CustomerService] f) =>
  PrEff f CustomerStore p p ()
invocationExample = do
  withStore (Proxy @"input.txt") $ Ix.do
    processCustomers (Proxy @"input.txt") (Proxy @"output.txt")

scopedProcessCustomers ::
  (Members [Writer [String], CustomerService] f) =>
  PrEff f CustomerStore p p ()
scopedProcessCustomers = Ix.do
  tell ["Hello, World!"]
  withStore (Proxy @"input.txt") $ Ix.do
    tell ["Start the processing!"]
    processCustomers (Proxy @"input.txt") (Proxy @"output.txt")
  tell ["Stop execution"]

-- >>> :t runIO . runWriter @[String] . runCustomerService $ runCustomerStoreIO scopedProcessCustomers
-- runIO . runWriter @[String] . runCustomerService $ runCustomerStoreIO scopedProcessCustomers :: IO ([String], ())
--
-- >>> run . runWriter @[String] . runState (Map.fromList [("input.txt", [()])]) . runCustomerService $ runCustomerStoreViaState scopedProcessCustomers
-- (["Hello, World!","Start the processing!","Stop execution"],(fromList [("input.txt",[()]),("output.txt",[()])],()))
--
