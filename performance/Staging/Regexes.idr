module Staging.Regexes

import Data.SnocList
import TyRE.Parser.Compile
import TyRE.Parser
import TyRE.Core
import TyRE.Extra.Elab
import TyRE.Extra.Idris
import Language.Reflection

import Data.SortedSet
import Data.DPair

import Data.Regex
import TyRE.StringRE
import Staging.ILexGenerated
import Text.ILex.Util

import Benchmark

%language ElabReflection

%runElab createTyREMod `{Staging.Generated}
    [`{TyRE.Core}, `{TyRE.StringRE}, `{Benchmark}, `{TyRE.Parser}, `{Staging.ILexGenerated}] `[
    repA : DontCompile $ TyRE (SnocList Unit)
    repA = Rep $ match 'a'

    repA' : TyRE (SnocList Unit)
    repA' = repA

    time : DontCompile $ TyRE (SnocList (Pair Nat Nat))
    time = Rep $
        Conv (Group $ (range '0' '1' <*> range '0' '9') `or` (range '2' '2' <*> range '0' '3')) cast
        <* match ':'
        <*> Conv (Group $ range '0' '5' <*> range '0' '9') cast

    time' : TyRE (SnocList (Pair Nat Nat))
    time' = time

    genAInput : Nat -> Maybe (List Char) -> List Char
    genAInput _ (Just xs) = 'a' :: xs
    genAInput k _ = replicate (k * 1000) 'a'

    genTimeInput : Nat -> Maybe (List Char) -> List Char
    genTimeInput _ (Just xs) = unpack "12:55" ++ xs
    genTimeInput k _ = concat $ List.replicate (k * 100) (unpack "12:55")

    export
    stagingBenchmarks : List Benchmark
    stagingBenchmarks =
        [ MkBench "staging.rep_a_interp" genAInput (pure . parseFull repA)
        -- , MkBench "staging.rep_a_compile" genAInput (pure . parseFull repA')
        , MkBench "staging.rep_a_ilex" genAInput (pure . lexRepA1)
        , MkBench "staging.time_interp" genTimeInput (pure . parseFull time)
        -- , MkBench "staging.time_compile" genTimeInput (pure . parseFull time')
        , MkBench "staging.time_ilex" genTimeInput (pure . lexTimes1)
        ]
]
