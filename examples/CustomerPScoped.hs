module CustomerPScoped where

import qualified Control.IxMonad as Ix
import CustomerEx
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

data Store inp
data Empty

data CustomerStore p q a where
  ReadStore :: (KnownSymbol inp) => proxy inp -> CustomerStore (Store inp) (Store inp) [Customer]
  WriteStore :: (KnownSymbol out) => proxy out -> [Customer] -> CustomerStore p (Store out) ()

data instance ScopeE CustomerStore m p p' q' q x' x where
  WithStore ::
    (KnownSymbol inp) =>
    proxy inp ->
    m (Store inp) (Store out) a ->
    ScopeE CustomerStore m p (Store inp) (Store out) q a ()

readStore :: (KnownSymbol inp) => proxy inp -> PrEff eff CustomerStore (Store inp) (Store inp) [Customer]
readStore p = sendP (ReadStore p)

writeStore :: (KnownSymbol out) => proxy out -> [Customer] -> PrEff eff CustomerStore p (Store out) ()
writeStore p c = sendP (WriteStore p c)

withStore :: (KnownSymbol inp) => proxy inp -> PrEff eff CustomerStore (Store inp) (Store out) x -> PrEff eff CustomerStore p q ()
withStore i m = sendScoped (WithStore i m)

runCustomerStoreIO ::
  (Member (Embed IO) f) =>
  PrEff f CustomerStore p q a ->
  PrEff f IVoid () () a
runCustomerStoreIO = interpretScoped
  (\case
      ReadStore (p :: proxy inp) -> Ix.do
        let fp = symbolVal p
        embed $ readCustomersIO fp
      WriteStore (p :: proxy out) cs -> Ix.do
        let fp = symbolVal p
        embed $ writeCustomersIO fp cs
  )
  (\k runner -> \case
    WithStore p m -> Ix.do
      let fp = symbolVal p
      embed (customersExistIO fp) >>= \case
        False ->
          runner $ runIKleisliTupled k ()
        True -> Ix.do
          _a <- runner m
          runner $ runIKleisliTupled k ()
  )

runCustomerStoreViaState ::
  (Member (State (Map FilePath [Customer])) f) =>
  PrEff f CustomerStore p q a ->
  PrEff f IVoid () () a
runCustomerStoreViaState = interpretScoped
  (\case
      ReadStore (p :: proxy inp) -> Ix.do
        let fp = symbolVal p
        s <- get
        pure $ s ! fp
      WriteStore (p :: proxy out) cs -> Ix.do
        let fp = symbolVal p
        s <- get
        put (insert fp cs s)
  )
  (\k runner -> \case
    WithStore p m -> Ix.do
      let fp = symbolVal p
      s <- get @(Map FilePath [Customer])
      case Map.lookup fp s of
        Nothing ->
          runner $ runIKleisliTupled k ()
        Just _ -> Ix.do
          _a <- runner m
          runner $ runIKleisliTupled k ()
  )

processCustomers' ::
  (Member CustomerService f, KnownSymbol inp, KnownSymbol out) =>
  proxy inp ->
  proxy out ->
  PrEff f CustomerStore (Store inp) (Store out) ()
processCustomers' inp out = Ix.do
  customers <- readStore inp
  newCustomers <- process customers
  writeStore out newCustomers

scopedProcessCustomers ::
  (Members [Writer [String], CustomerService] f) =>
  PrEff f CustomerStore Empty Empty ()
scopedProcessCustomers = Ix.do
  tell ["Hello, World!"]
  withStore (Proxy @"input.txt") $ Ix.do
    tell ["Start the processing!"]
    processCustomers' (Proxy @"input.txt") (Proxy @"output.txt")
  tell ["Stop execution"]

-- >>> :t runIO . runCustomerService $ runCustomerStoreIO scopedProcessCustomers
-- runIO . runCustomerService $ runCustomerStoreIO scopedProcessCustomers :: IO ()
--
-- >>> run . runWriter @[String] . runState (Map.fromList [("input.txt", [()])]) . runCustomerService $ runCustomerStoreViaState scopedProcessCustomers
-- (["Hello, World!","Start the processing!","Stop execution"],(fromList [("input.txt",[()]),("output.txt",[()])],()))
--
