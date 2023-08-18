import PrEff

main :: IO ()
main = pure ()

type Customer = ()

data CustomerService a where
  Process :: [Customer] -> CustomerService [Customer]

data CustomerDb a where
  ReadCustomers :: FilePath -> CustomerDb [Customer]
  WriteCustomers :: FilePath -> [Customer] -> CustomerDb ()

runCustomerServiceIO ::
  (Member (Embed IO) f, ScopedEffect s) =>
  PrEff (CustomerService : f) s p q x ->
  PrEff f s p q x
runCustomerServiceIO = interpret $ \case
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

processData :: [Customer] -> [Customer]
processData = undefined

readCustomersIO :: FilePath -> IO [Customer]
readCustomersIO = undefined

writeCustomersIO :: FilePath -> [Customer] -> IO ()
writeCustomersIO = undefined
