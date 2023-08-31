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
    m () () () ->
    ScopeE CustomerStore m p () () q () ()

readStore :: FilePath -> PrEff eff CustomerStore () () [Customer]
readStore p = sendP (ReadStore p)

writeStore :: FilePath -> [Customer] -> PrEff eff CustomerStore () () ()
writeStore p c = sendP (WriteStore p c)

withStore :: FilePath -> PrEff eff CustomerStore () () () -> PrEff eff CustomerStore () () ()
withStore i m = sendScoped (WithStore i m)

runCustomerStoreIO ::
  (Member (Embed IO) f) =>
  PrEff f CustomerStore p q a ->
  PrEff f IVoid () () a
runCustomerStoreIO = interpretScopedH
  (\case
      ReadStore fp -> Ix.do
        embed $ readCustomersIO fp
      WriteStore fp cs -> Ix.do
        embed $ writeCustomersIO fp cs
  )
  (\runner -> \case
    WithStore fp m -> Ix.do
      embed (customersExistIO fp) >>= \case
        True -> Ix.do
          runner m

        False -> Ix.do
          pure ()
  )

runCustomerStoreViaState ::
  (Member (State (Map FilePath [Customer])) f) =>
  PrEff f CustomerStore p q a ->
  PrEff f IVoid () () a
runCustomerStoreViaState = interpretScopedH
  (\case
      ReadStore fp -> Ix.do
        s <- get
        pure $ s ! fp
      WriteStore fp cs -> Ix.do
        s <- get
        put (insert fp cs s)
  )
  (\runner -> \case
    WithStore fp m -> Ix.do
      s <- get @(Map FilePath [Customer])
      case Map.lookup fp s of
        Nothing ->
          pure ()

        Just _ -> Ix.do
          runner m
  )

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
