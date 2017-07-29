
module SQL

import Data.HVect

-- Tables

||| Tables/relations.
record Table (xs : Vect n Type) where
  constructor MkTable

  ||| The names of constituent tables.
  names : List String
  types : HVect xs

-- TODO labels/extensible records http://lpaste.net/104020

||| Constructor for a single table
table : String -> HVect xs -> Table xs
table x y = MkTable [x] y

||| Constructor for a product of tables
product : List String -> HVect xs -> Table xs
product = MkTable

Show (Table xs) where
  show = pack . intercalate [',', ' '] . map unpack . toList . names

-- Is there a more precise name?
merge : Table xs -> Table ys -> Table (xs ++ ys)
merge xs ys = product (names xs ++ names ys) (types xs ++ types ys)

-- Rows

Row : Vect n Type -> Type
Row = HVect

-- SQL

data SQL : Table xs -> Type where
  From : (a : Table xs) -> (b : Table ys) -> SQL (merge a b)

Show (SQL t) where
  show (From a b) = "(select * from " ++ show a ++ ", " ++ show b ++ ")"

-- Domain types

data PersonId = Id Int
Show PersonId where
  show (Id n) = show n

data Person = Elizabeth
Show Person where
  show _ = "Elizabeth"

data Birthday = Day String
Show Birthday where
  show (Day s) = s

-- Table definitions

people : Table [Type, Type]
people = table "people" [PersonId, Person]

birthdays : Table [Type, Type]
birthdays = table "birthdays" [PersonId, Birthday]

-- An SQL fragment. Needs to be run to produce a value

fromClause : SQL (product ["people", "birthdays"] [PersonId, Person, PersonId, Birthday])
fromClause = From people birthdays

-- Example usage

-- TODO make this more generic
runSQL : SQL (product ["people", "birthdays"] [PersonId, Person, PersonId, Birthday]) ->
          IO (List (Row [PersonId, Person, PersonId, Birthday]))
runSQL sql = do
  printLn $ "running: " ++ show sql
  pure [
    [Id 1, Elizabeth, Id 2, Day "asd"],
    [Id 2, Elizabeth, Id 3, Day "lkj"]]

main : IO ()
main = do
  runSQL fromClause >>= printLn
