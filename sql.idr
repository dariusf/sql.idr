
module SQL

import Data.HVect

Table : Vect n Type -> Type
Table = HVect

Row : Vect n Type -> Type
Row = HVect

data SQL : Table xs -> Type where
  From : (a : Table xs) -> (b : Table ys) -> SQL (a ++ b)

-- Domain types
data PersonId = Id Int
data Person = Elizabeth
data Birthday = Day String

-- Table definitions. Probably can be generated somehow
people : Table [Type, Type]
people = [PersonId, Person]

people1 : Table [PersonId, Person]
people1 = [Id 1, Elizabeth]

birthdays : Table [Type, Type]
birthdays = [PersonId, Birthday]

-- An SQL fragment. Needs to be run to produce a value
fromClause : SQL [PersonId, Person, PersonId, Birthday]
fromClause = From people birthdays

TupleVect : (n:Nat) -> Type -> Type
TupleVect Z t = ()
TupleVect (S k) t = (t, TupleVect k t)

testTV : TupleVect 4 Nat
testTV = (1, 2, 3, 4, ())

runSQL : {xs : HVect ts} -> SQL xs -> List (HVect ts)
runSQL {xs} _ = [xs, xs]

result : (PersonId, Person, PersonId, Birthday)
result = (Id 1, Elizabeth, Id 1, Day "monday")

-- This is a better idea than tuples
result1 : HVect [PersonId, Person, PersonId, Birthday]
result1 = [Id 1, Elizabeth, Id 1, Day "monday"]

-- How to cover the concrete types?
howToRecover : (List (HVect [Type, Type, Type, Type]))
howToRecover = runSQL fromClause

