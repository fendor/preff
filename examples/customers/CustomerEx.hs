{-# LANGUAGE EmptyDataDecls #-}
{-# OPTIONS_GHC -Wno-unused-top-binds #-}

module CustomerEx where

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

data CustomerDb a where
  ReadCustomers :: FilePath -> CustomerDb [Customer]
  WriteCustomers :: FilePath -> [Customer] -> CustomerDb ()

readCustomers :: (Member CustomerDb f) => FilePath -> PrEff f s p p [Customer]
readCustomers fp = send (ReadCustomers fp)

writeCustomers :: (Member CustomerDb f) => FilePath -> [Customer] -> PrEff f s p p ()
writeCustomers fp cs = send (WriteCustomers fp cs)

runCustomerDbIO ::
  (Member (Embed IO) f, ScopedEffect s) =>
  PrEff (CustomerDb : f) s p q x ->
  PrEff f s p q x
runCustomerDbIO = interpret $ \case
  ReadCustomers fp ->
    embed $ readCustomersIO fp
  WriteCustomers fp customers ->
    embed $ writeCustomersIO fp customers

runCustomerDbViaState ::
  (Member (State (Map FilePath [Customer])) f, ScopedEffect s) =>
  PrEff (CustomerDb : f) s p q x ->
  PrEff f s p q x
runCustomerDbViaState = interpret $ \case
  ReadCustomers fp -> do
    customerMap <- get
    pure (customerMap ! fp)
  WriteCustomers fp customers -> do
    customerMap <- get
    put (insert fp customers customerMap)
    pure ()

processCustomers ::
  (Members '[CustomerService, CustomerDb] f) =>
  FilePath ->
  FilePath ->
  PrEff f s p p ()
processCustomers inp out = do
  customers <- readCustomers inp
  newCustomers <- process customers
  writeCustomers out newCustomers
