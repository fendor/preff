module Utils where
import PrEff
import System.Directory

type Customer = ()

processData :: [Customer] -> [Customer]
processData = id

customersExistIO :: FilePath -> IO Bool
customersExistIO = doesFileExist

readCustomersIO :: FilePath -> IO [Customer]
readCustomersIO fp = readFile fp >> pure []

writeCustomersIO :: FilePath -> [Customer] -> IO ()
writeCustomersIO fp cs = writeFile fp ""

data CustomerService a where
  Process :: [Customer] -> CustomerService [Customer]

process :: Member CustomerService eff => [Customer] -> PrEff eff s p p [Customer]
process cs = send (Process cs)

runCustomerService ::
  (ScopedEffect s) =>
  PrEff (CustomerService : f) s p q x ->
  PrEff f s p q x
runCustomerService = interpret $ \case
  Process customers ->
    pure $ processData customers
