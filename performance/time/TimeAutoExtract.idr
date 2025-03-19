import Data.Regex

timeRE : TyRE (SnocList (Nat, Nat))
timeRE = Rep $
    map f (r "([01][0-9])!" `or` r "([2][0-3])!")
    <*> map f (r ":([0-5][0-9])!")
  where
    digit : Char -> Nat
    digit c = cast c `minus` cast '0'

    f : (Char, Char) -> Nat
    f (c1, c2) = 10 * digit c1 + digit c2

main : IO ()
main = do
    str <- getLine
    case parse timeRE str of
        Nothing => putStrLn "Error"
        Just _ => putStrLn "Ok"
