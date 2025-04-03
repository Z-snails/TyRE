module Time

import Data.Regex
import Data.Stream

import Benchmark

autoRE : TyRE (SnocList (Nat, Nat))
autoRE = Rep $
    map f (r "([01][0-9])!" `or` r "([2][0-3])!")
    <*> map f (r ":([0-5][0-9])!")
  where
    digit : Char -> Nat
    digit c = cast c `minus` cast '0'

    f : (Char, Char) -> Nat
    f (c1, c2) = 10 * digit c1 + digit c2

manualRE : TyRE (List (String, String))
manualRE = r "(`([01][0-9])|([2][0-3])`:`[0-5][0-9]`)*"

extract : (String, String) -> (Nat, Nat)
extract (h, m) = (cast h, cast m)

matchRE : TyRE ()
matchRE = ignore autoRE

times : Stream String
times = cycle ["00:00", "10:36", "22:44"]

genInput : Nat -> Maybe String -> String
genInput k (Just s) = index k times ++ s
genInput _ Nothing = ""

export
timeBenchmarks : List Benchmark
timeBenchmarks =
    [ MkBench "time.auto" genInput (pure . parse autoRE)
    , MkBench "time.manual" genInput (pure . map (map extract) . parse manualRE)
    , MkBench "time.match" genInput (pure . parse matchRE)
    ]
