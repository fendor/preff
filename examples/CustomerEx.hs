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

processCustomers ::
  (Members '[CustomerService, CustomerDb] f) =>
  FilePath ->
  FilePath ->
  PrEff f s p p ()
processCustomers inp out = do
  customers <- readCustomers inp
  newCustomers <- process customers
  writeCustomers out newCustomers
