
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

hline : (edge : Char) -> (body : Char) -> (n : Nat) -> {auto np : 2 `LTE` n} -> String
hline e b n = pack (e :: (replicate (n - 2) b) ++ [e])

drawBox : (x : Nat) -> (y : Nat) -> {auto xp : 2 `LTE` x} -> {auto yp : 2 `LTE` y} -> List String
drawBox x y = hline '+' '-' x :: (replicate (y - 2) $ hline '|' ' ' x) ++ [hline '+' '-' x]

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
