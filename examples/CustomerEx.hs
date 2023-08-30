{-# LANGUAGE EmptyDataDecls #-}
{-# OPTIONS_GHC -Wno-unused-top-binds #-}

module CustomerEx where

import qualified Control.IxMonad as Ix
import PrEff
import PrEff.Simple.State
import System.FilePath
import Data.Map
import qualified Data.Text as T
import Data.Proxy
import GHC.TypeLits
import System.Directory (doesFileExist)
import qualified Data.Map as Map
import PrEff.Simple.Writer

main :: IO ()
main = putStrLn "Hello, World!"

type Customer = ()

data CustomerService a where
  Process :: [Customer] -> CustomerService [Customer]

process :: Member CustomerService eff => [Customer] -> PrEff eff s p p [Customer]
process cs = send (Process cs)

data CustomerDb a where
  ReadCustomers :: FilePath -> CustomerDb [Customer]
  WriteCustomers :: FilePath -> [Customer] -> CustomerDb ()

readCustomers :: Member CustomerDb f => FilePath -> PrEff f s p p [Customer]
readCustomers fp = send (ReadCustomers fp)

writeCustomers :: Member CustomerDb f => FilePath -> [Customer] -> PrEff f s p p ()
writeCustomers fp cs = send (WriteCustomers fp cs)

data Open
data Closed

data DbHandle p q a where
  Read :: FilePath -> DbHandle Open Open T.Text
  Write :: FilePath -> T.Text -> DbHandle Open Open ()

data instance ScopeE DbHandle m p p' q' q x x' where
  WithDb ::
    FilePath ->
    m Open q x ->
    ScopeE DbHandle m p p q Closed x x

runCustomerService ::
  (ScopedEffect s) =>
  PrEff (CustomerService : f) s p q x ->
  PrEff f s p q x
runCustomerService = interpret $ \case
  Process customers ->
    pure $ processData customers

runCustomerDbIO :: (Member (Embed IO) f, ScopedEffect s) =>
  PrEff (CustomerDb : f) s p q x ->
  PrEff f s p q x
runCustomerDbIO  = interpret $ \case
  ReadCustomers fp ->
    embed $ readCustomersIO fp
  WriteCustomers fp customers ->
    embed $ writeCustomersIO fp customers

runCustomerDbViaState ::
  (Member (State (Map FilePath [Customer])) f, ScopedEffect s) =>
  PrEff (CustomerDb : f) s p q x ->
  PrEff f s p q x
runCustomerDbViaState  = interpret $ \case
  ReadCustomers fp -> do
    customerMap <- get
    pure (customerMap ! fp)
  WriteCustomers fp customers -> do
    customerMap <- get
    put (insert fp customers customerMap)
    pure ()

processData :: [Customer] -> [Customer]
processData = id

customersExistIO :: FilePath -> IO Bool
customersExistIO = doesFileExist

readCustomersIO :: FilePath -> IO [Customer]
readCustomersIO fp = readFile fp >> pure []

writeCustomersIO :: FilePath -> [Customer] -> IO ()
writeCustomersIO fp cs = writeFile fp ""

data Store inp
data Empty

data CustomerStore p q a where
  ReadStore ::  KnownSymbol inp => proxy inp -> CustomerStore (Store inp) (Store inp) [Customer]
  WriteStore :: KnownSymbol out => proxy out -> [Customer] -> CustomerStore p (Store out) ()

data instance ScopeE CustomerStore m p p' q' q x' x where
  WithStore ::
    KnownSymbol inp =>
    proxy inp ->
    m (Store inp) (Store out) a ->
    ScopeE CustomerStore m p (Store inp) (Store out) q a ()

readStore :: KnownSymbol inp => proxy inp -> PrEff eff CustomerStore (Store inp) (Store inp) [Customer]
readStore p = sendP (ReadStore p)

writeStore :: KnownSymbol out => proxy out -> [Customer] -> PrEff eff CustomerStore p (Store out) ()
writeStore p c = sendP (WriteStore p c)

withStore :: KnownSymbol inp => proxy inp -> PrEff eff CustomerStore (Store inp) (Store out) x -> PrEff eff CustomerStore p q ()
withStore i m = sendScoped (WithStore i m)

runCustomerStoreIO ::
  Member (Embed IO) f =>
  PrEff f CustomerStore p q a ->
  PrEff f IVoid () () a
runCustomerStoreIO = \case
  Value a -> pure a
  Impure op k ->
    Impure op $
      IKleisliTupled $ \x -> runCustomerStoreIO $ runIKleisliTupled k x
  ImpureP op k ->
    case op of
      ReadStore (p :: proxy inp) -> Ix.do
        let fp = symbolVal p
        cs <- embed $ readCustomersIO fp
        runCustomerStoreIO $ runIKleisliTupled k cs
      WriteStore (p :: proxy out) cs -> Ix.do
        let fp = symbolVal p
        r <- embed $ writeCustomersIO fp cs
        runCustomerStoreIO $ runIKleisliTupled k r
  ScopedP (WithStore p m) k -> Ix.do
    let fp = symbolVal p
    embed (customersExistIO fp) >>= \case
      False ->
        runCustomerStoreIO $ runIKleisliTupled k ()
      True -> Ix.do
        _a <- runCustomerStoreIO m
        runCustomerStoreIO $ runIKleisliTupled k ()

runCustomerStoreViaState ::
  Member (State (Map FilePath [Customer])) f =>
  PrEff f CustomerStore p q a ->
  PrEff f IVoid () () a
runCustomerStoreViaState = \case
  Value a -> pure a
  Impure op k ->
    Impure op $
      IKleisliTupled $ \x -> runCustomerStoreViaState $ runIKleisliTupled k x
  ImpureP op k ->
    case op of
      ReadStore (p :: proxy inp) -> Ix.do
        let fp = symbolVal p
        s <- get
        let cs = s ! fp
        runCustomerStoreViaState $ runIKleisliTupled k cs
      WriteStore (p :: proxy out) cs -> Ix.do
        let fp = symbolVal p
        s <- get
        r <- put (insert fp cs s)
        runCustomerStoreViaState $ runIKleisliTupled k r
  ScopedP (WithStore p m) k -> Ix.do
    let fp = symbolVal p
    s <- get @(Map FilePath [Customer])
    case Map.lookup fp s of
      Nothing ->
        runCustomerStoreViaState $ runIKleisliTupled k ()
      Just _ -> Ix.do
        _a <- runCustomerStoreViaState m
        runCustomerStoreViaState $ runIKleisliTupled k ()

processCustomers ::
  (Members '[CustomerService, CustomerDb] f) =>
  FilePath ->
  FilePath ->
  PrEff f s p p ()
processCustomers inp out = do
  customers <- readCustomers inp
  newCustomers <- process customers
  writeCustomers out newCustomers

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
  Members [Writer [String], CustomerService] f =>
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
