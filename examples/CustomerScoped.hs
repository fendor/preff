module CustomerScoped where

import qualified Control.IxMonad  as Ix
import CustomerEx
import Data.Map
import qualified Data.Map as Map
import Data.Proxy
import qualified Data.Text  as T
import GHC.TypeLits
import PrEff
import PrEff.Simple.State
import PrEff.Simple.Writer
import System.Directory (doesFileExist)
import System.FilePath

data CustomerStore p q a where
  ReadStore :: FilePath -> CustomerStore () () [Customer]
  WriteStore :: FilePath -> [Customer] -> CustomerStore () () ()

data instance ScopeE CustomerStore m p p' q' q x' x where
  WithStore ::
    FilePath ->
    m () () a ->
    ScopeE CustomerStore m p () () q a ()

readStore :: FilePath -> PrEff eff CustomerStore () () [Customer]
readStore p = sendP (ReadStore p)

writeStore :: FilePath -> [Customer] -> PrEff eff CustomerStore () () ()
writeStore p c = sendP (WriteStore p c)

withStore :: FilePath -> PrEff eff CustomerStore () () x -> PrEff eff CustomerStore () () ()
withStore i m = sendScoped (WithStore i m)

runCustomerStoreIO ::
  (Member (Embed IO) f) =>
  PrEff f CustomerStore p q a ->
  PrEff f IVoid () () a
runCustomerStoreIO = \case
  Value a -> pure a
  Impure op k ->
    Impure op
      $ IKleisliTupled
      $ \x -> runCustomerStoreIO $ runIKleisliTupled k x
  ImpureP op k ->
    case op of
      ReadStore fp -> Ix.do
        cs <- embed $ readCustomersIO fp
        runCustomerStoreIO $ runIKleisliTupled k cs
      WriteStore fp cs -> Ix.do
        r <- embed $ writeCustomersIO fp cs
        runCustomerStoreIO $ runIKleisliTupled k r
  ScopedP (WithStore fp m) k -> Ix.do
    embed (customersExistIO fp) >>= \case
      False ->
        runCustomerStoreIO $ runIKleisliTupled k ()
      True -> Ix.do
        _a <- runCustomerStoreIO m
        runCustomerStoreIO $ runIKleisliTupled k ()

runCustomerStoreViaState ::
  (Member (State (Map FilePath [Customer])) f) =>
  PrEff f CustomerStore p q a ->
  PrEff f IVoid () () a
runCustomerStoreViaState = \case
  Value a -> pure a
  Impure op k ->
    Impure op
      $ IKleisliTupled
      $ \x -> runCustomerStoreViaState $ runIKleisliTupled k x
  ImpureP op k ->
    case op of
      ReadStore fp -> Ix.do
        s <- get
        let cs = s ! fp
        runCustomerStoreViaState $ runIKleisliTupled k cs
      WriteStore fp cs -> Ix.do
        s <- get
        r <- put (insert fp cs s)
        runCustomerStoreViaState $ runIKleisliTupled k r
  ScopedP (WithStore fp m) k -> Ix.do
    s <- get @(Map FilePath [Customer])
    case Map.lookup fp s of
      Nothing ->
        runCustomerStoreViaState $ runIKleisliTupled k ()
      Just _ -> Ix.do
        _a <- runCustomerStoreViaState m
        runCustomerStoreViaState $ runIKleisliTupled k ()

processCustomers' ::
  (Member CustomerService f) =>
  FilePath ->
  FilePath ->
  PrEff f CustomerStore () () ()
processCustomers' inp out = do
  withStore inp $ do
    customers <- readStore inp
    newCustomers <- process customers
    writeStore out newCustomers
