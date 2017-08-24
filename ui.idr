
import Data.Vect
import Data.So

infixl 6 //
data Ratio = (//) Nat Nat

Fractional Nat where
  _ / Z = Z
  a / b =
    case b `isLTE` a of
      Yes p => assert_total (1 + (a - b) / b)
      No _ => Z

mul : Ratio -> Nat -> Nat
mul (i // j) k = (i * k) / j

data Prim = Box

data Layout
  = Only Prim
  | Adj Ratio Layout Layout
  | Stack Ratio Layout Layout
  | Overlay Layout Layout
  -- | Scale Double Layout

combine : List String -> List String -> List String
combine [] [] = []
combine [] (x :: xs) = x :: (combine [] xs)
combine (x :: xs) [] = x :: (combine xs [])
combine (x :: xs) (y :: ys) = (x ++ y) :: combine xs ys

Line : Nat -> Type
Line x = Vect x Char

Grid : Nat -> Nat -> Type
Grid x y = Vect y (Line x)

adj : Grid x y -> Grid z y -> Grid (x + z) y
adj [] [] = []
adj (x :: xs) (y :: ys) = (x ++ y) :: adj xs ys

stack : Grid x y -> Grid x z -> Grid x (y + z)
stack [] [] = []
stack xs ys = xs ++ ys

||| The left argument goes on top
overlay : Grid x y -> Grid x y -> Grid x y
overlay [] [] = []
overlay (x :: xs) (y :: ys) = ol x y :: overlay xs ys
  where
    ol : Line n -> Line n -> Line n
    ol [] [] = []
    ol (' ' :: xs) (y :: ys) = y :: ol xs ys
    ol (x :: xs) (_ :: ys) = x :: ol xs ys

render'' : Grid x y -> String
render'' = unlines . toList . map pack

ltv : (xs : List a) -> Vect (length xs) a
ltv [] = []
ltv (x :: xs) = x :: ltv xs

pad : a -> (n : Nat) -> List a -> Vect n a
pad a n xs =
  let xn = length xs in
  case xn `isLTE` n of
    Yes _ =>
      let left = (n - xn) / 2 in
      case left `isLTE` (n - xn) of
        Yes _ =>
          let right = (n - xn) - left in
          -- case choose (n == left + length xs + right) of
          case decEq n (left + (length xs + right)) of
            Yes p =>
              rewrite p in
              replicate left a ++ ltv xs ++ replicate right a
            No _ => ?uhoh
        No _ => ?dead2
    No _ => ?dead1

padGrid : (x : Nat) -> (y : Nat) -> List (List Char) -> Grid x y
padGrid x y xss = pad (replicate x ' ') y $ map (pad ' ' x) xss

hline : (edge : Char) -> (body : Char) -> (n : Nat) -> {auto np : 2 `LTE` n} -> String
hline e b n = with List (pack (e :: (replicate (n - 2) b) ++ [e]))

hline' : (edge : Char) -> (body : Char) -> (n : Nat) -> {auto np : 2 `LTE` n} -> Line n
hline' e b n =
  case decEq n (S (n - 2 + 1)) of
    Yes p => rewrite p in (e :: (replicate (n - 2) b) ++ [e])
    No _ => idris_crash ":("

drawBox : (x : Nat) -> (y : Nat) -> {auto xp : 2 `LTE` x} -> {auto yp : 2 `LTE` y} -> List String
drawBox x y = hline '+' '-' x :: (replicate (y - 2) $ hline '|' ' ' x) ++ [hline '+' '-' x]

plusMinusElim : (n : Nat) -> {auto np : 1 `LTE` n} -> n = (n - 1) + 1
plusMinusElim Z impossible
plusMinusElim (S k) =
  rewrite minusZeroRight k in
  rewrite plusCommutative k 1 in
  Refl

sigh : (y : Nat) -> {auto yp : 2 `LTE` y} -> y = (S (y - 2 + 1))
sigh Z impossible
sigh (S y') {yp = (LTESucc _)} =
  rewrite plusMinusElim y' in Refl

drawBox' : (x : Nat) -> (y : Nat) -> {auto xp : 2 `LTE` x} -> {auto yp : 2 `LTE` y} -> Grid x y
drawBox' x y =
  rewrite sigh y in
  hline' '+' '-' x :: (replicate (y - 2) $ hline' '|' ' ' x) ++ [hline' '+' '-' x]

render2 : (x : Nat) -> (y : Nat) -> {auto xp : 2 `LTE` x} -> {auto yp : 2 `LTE` y} -> Layout -> Grid x y
render2 x y (Only z) = drawBox' x y
render2 x y (Adj z w s) =
  case (mul z x) `isLTE` x of
    Yes _ =>
      case 2 `isLTE` (mul z x) of
        Yes _ =>
          case 2 `isLTE` (x - mul z x) of
            Yes _ =>
              case decEq x (mul z x + (x - mul z x)) of
                Yes p => rewrite p in adj (render2 (mul z x) y w) (render2 (x - mul z x) y s)
                No _ => idris_crash ":\\"
            No _ => ?uh
        No _ => ?wut
    No _ => ?huh
render2 x y (Stack z w s) =
  case (mul z y) `isLTE` y of
    Yes _ =>
      case 2 `isLTE` (mul z y) of
        Yes _ =>
          case 2 `isLTE` (y - mul z y) of
            Yes _ =>
              case decEq y (mul z y + (y - mul z y)) of
                Yes p => rewrite p in render2 x (mul z y) w ++ render2 x (y - mul z y) s
                No _ => idris_crash "/:"
            No _ => ?ugh
        No _ => ?alksdj
    No _ => ?asd
-- render2 x y (Overlay z w) = ?overlay

render' : (x : Nat) -> (y : Nat) -> {auto xp : 2 `LTE` x} -> {auto yp : 2 `LTE` y} -> Layout -> List String
render' x y (Only z) = drawBox x y
render' x y (Adj z w s) =
  case (mul z x) `isLTE` x of
    Yes _ =>
      case 2 `isLTE` (mul z x) of
        Yes _ =>
          case 2 `isLTE` (x - mul z x) of
            Yes _ => combine (render' (mul z x) y w) (render' (x - mul z x) y s)
            No _ => ?uh
        No _ => ?wut
    No _ => ?huh
render' x y (Stack z w s) =
  case (mul z y) `isLTE` y of
    Yes _ =>
      case 2 `isLTE` (mul z y) of
        Yes _ =>
          case 2 `isLTE` (y - mul z y) of
            Yes _ => render' x (mul z y) w ++ render' x (y - mul z y) s
            No _ => ?ugh
        No _ => ?alksdj
    No _ => ?asd
render' x y (Overlay z w) = ?overlay

render : (x : Nat) -> (y : Nat) -> {auto xp : 2 `LTE` x} -> {auto yp : 2 `LTE` y} -> Layout -> String
render x y = pack . intercalate ['\n'] . map unpack . render' x y

main : IO ()
main = do
  putStrLn $ render 6 6 $ Only Box
  putStrLn $ render 80 25 $ Adj (1 // 2) (Only Box) (Stack (1 // 3) (Only Box) (Only Box))

  putStrLn $ render'' $ render2 6 6 $ Only Box
  putStrLn $ render'' $ render2 80 25 $ Adj (1 // 2) (Only Box) (Stack (1 // 3) (Only Box) (Only Box))
