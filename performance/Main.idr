module Main

import Data.List
import Data.Maybe
import Data.String
import System

import Benchmark

import Staging.Regexes -- ensure Staging.Generated gets regenerated if required
import Staging.Generated
import Group
import CombCompare
import Time

benchmarks : List Benchmark
benchmarks = concat
    [ stagingBenchmarks
    , groupBenchmarks
    , combCompareBenchmarks
    , timeBenchmarks
    ]

usage : String
usage = """
bench <COMMAND>

Available commands:
- help: print this message
- list: print available benchmarks
- <BENCHMARK>: run the given benchmark

Available benchmarks:
\{concat $ map (\b => "- \{b.name}\n") benchmarks}
"""

find : (arg : String) -> List String -> Maybe Nat
find arg (key :: val :: args) = if arg == key
    then guard (all isDigit (unpack val)) $> cast val
    else find arg (val :: args)
find _ _ = Nothing

main : IO ()
main = do
    _ :: cmd :: args <- getArgs
        | _ => putStrLn usage
    let max = fromMaybe 1000 $ find "--max" args
    let samples = fromMaybe 20 $ find "--samples" args
    case cmd of
        "help" => putStrLn usage
        "list" => putStr $ unlines $ map (.name) benchmarks
        _ => case find (\b => b.name == cmd) benchmarks of
            Nothing => putStrLn usage
            Just bench => do
                printHeader
                time bench max samples
