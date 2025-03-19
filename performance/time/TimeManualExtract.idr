import Data.Regex

timeRE : TyRE (SnocList (String, String))
timeRE = r "(`([01][0-9])|([2][0-3])`:`[0-5][0-9]`)*"

extract : (String, String) -> (Nat, Nat)
extract (h, m) = (cast h, cast m)

main : IO ()
main = do
    str <- getLine
    case map (map extract) $ parse timeRE str of
        Nothing => putStrLn "Error"
        Just _ => putStrLn "Ok"
