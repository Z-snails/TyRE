module Test

import System.Clock
import TyRE.Parser.Compile
import TyRE.Parser

import Data.List
import Data.Regex
import Language.Reflection

import Data.Fin
import Data.SortedSet
import Data.DPair
import Data.SnocList
import Syntax.PreorderReasoning

import TyRE.Core
import TyRE.Parser.GroupThompson
import public TyRE.Parser.Compile.Runtime

import Data.Regex

%language ElabReflection

timeRE : TyRE (SnocList (Nat, Nat))
timeRE = Rep $
    Conv
        ( (MatchChar (Range ('0', '1')) <*> MatchChar (Range ('0', '9')))
        `or` (MatchChar (Range ('2', '2')) <*> MatchChar (Range ('0', '3')))
        ) f
    -- <* MatchChar (Range (':', ':'))
    <*> Conv
        (MatchChar (Range ('0', '5')) <*> MatchChar (Range ('0', '9')))
        f
  where
    digit : Char -> Nat
    digit c = cast c `minus` cast '0'

    f : (Char, Char) -> Nat
    f (c1, c2) = 10 * digit c1 + digit c2

-- %logging "eval" 100

timeCompiled : CompiledSM (SnocList (Nat, Nat))
-- timeCompiled = %runElab doCompile timeRE

simple : CompiledSM Unit
simple = %runElab doCompile Empty

-- %logging off

input : List Char
input = concat $ List.replicate 10000 (unpack "12:45")

time : String -> (List Char -> IO (Maybe a)) -> IO ()
time name fun = do
    let i = input
    start <- clockTime Monotonic
    res <- fun i
    end <- clockTime Monotonic
    let res = the String $ case res of
            Just _ => "ok"
            Nothing => "err"
    let diff = timeDifference end start
    putStrLn "\{name} took \{show diff} - \{res}"

main : IO ()
-- main = do
--     time "interp" (pure . parseFull timeRE)
--     time "stage" (pure . parseFull timeCompiled)
    -- if mode == "stage"
    --     then case parseFull timeCompiled input of
    --         Just _ => putStrLn "stage Ok"
    --         Nothing => putStrLn "stage Err"
    --     else case Parser.parseFull timeRE input of
    --         Just _ => putStrLn "interp Ok"
    --         Nothing => putStrLn "interp Err"
