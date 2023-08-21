import PrEff
import PrEff.Simple.State
import System.FilePath
import Data.Map

main :: IO ()
main = pure ()

type Customer = ()

data CustomerService a where
  Process :: [Customer] -> CustomerService [Customer]

data CustomerDb a where
  ReadCustomers :: FilePath -> CustomerDb [Customer]
  WriteCustomers :: FilePath -> [Customer] -> CustomerDb ()

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
processData = undefined

readCustomersIO :: FilePath -> IO [Customer]
readCustomersIO = undefined

writeCustomersIO :: FilePath -> [Customer] -> IO ()
writeCustomersIO = undefined
