
-- http://lpaste.net/104020
-- https://groups.google.com/forum/m/#!topic/idris-lang/FiXh78d0C2Y
-- https://gist.github.com/jroesch/31c311bcb28711d3ee2a

data HList : List Type -> Type where
  Nil : HList []
  (::) : a -> HList xs -> HList (a::xs)

head : HList (x::xs) -> x
head (x::_) = x

tail : HList (x::xs) -> HList xs
tail (_::y) = y

test : HList [Integer, String, Bool]
test = [1, "hi", True]

test1 : HList [String, Bool]
test1 = tail test

append : HList xs -> HList ys -> HList (xs ++ ys)
append [] y = y
append (x::z) y = x :: (append z y)

-- Requires dependent pattern matching?
-- foldr : (a -> b -> c) -> c -> HList as -> c
-- foldr f empty [] = empty
-- foldr f empty (x :: y) = f x (foldr f empty y)

huh : (HList ([String, Integer] ++ [Bool] ++ [Integer]))
huh = append ["1", 1] (append [True] [2])

Table : List Type -> Type
Table = HList

data SQL : Table xs -> Type where
  From : (a : Table xs) -> (b : Table ys) -> SQL (append a b)

-- Domain types
data PersonId = Id Int
data Person = Elizabeth
data Birthday = Day String

-- Table definitions. Probably can be generated somehow
people : Table [Type, Type]
people = [PersonId, Person]

birthdays : Table [Type, Type]
birthdays = [PersonId, Birthday]

-- An SQL fragment. Needs to be run to produce a value
fromClause : SQL [PersonId, Person, PersonId, Birthday]
fromClause = From people birthdays

-- VarInt: Nat -> Type
-- VarInt Z     = Int
-- VarInt (S n) = Int -> VarInt n

-- adder: (n: Nat) -> Int -> VarInt n
-- adder Z     acc = acc
-- adder (S m) acc = holeadder_rhs_2

-- valueTypes : HList a -> -> Type
-- valueTypes [] = Void
-- valueTypes xs =

-- runSQL : SQL xs -> xs
