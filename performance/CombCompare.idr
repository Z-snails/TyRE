module CombCompare

import Data.List
import Data.String
import Data.Regex

import Benchmark

import AltComb
import ConcatComb
import ConcatTyRE
import StarComb
import StarComb2

a_star : TyRE Nat
a_star = r "(a*)!"

||| regex: ((a*c)|a)*b -> counts the number of a's
a_star2 : TyRE Nat
a_star2 = sum `map`
    rep0
        ( r "(a*)!c"
        `or` (const 1 `map` match 'a'))
    <* match 'b'

||| regex: a(|a)^n
rightRE : Nat -> TyRE Nat
rightRE 0 = const 0 `map` match 'a'
rightRE (S k) =
    (const 0 `map` match 'a')
    `or` ((+ 1) `map` rightRE k)

export
combCompareBenchmarks : List Benchmark
combCompareBenchmarks =
    [ MkBench "concat_comb" ConcatComb.getInput (pure . ConcatComb.run)
    , MkBench "concat_tyre"
        {input = (n : Nat ** (TyRE (ConcatTyRE.shape n), String))}
        (\n, _ => (n ** (createRE n, replicate n 'a')))
        (\(n ** (re, inp)) => pure $ ignore $ parse re inp)

    , MkBench "star_comb" (\n, _ => replicate n 'a') (pure . StarComb.run)
    , MkBench "star_tyre" (\n, _ => replicate n 'a') (pure . parse a_star)

    , MkBench "star_comb2" (\n, _ => replicate n 'a') (pure . StarComb2.run)
    , MkBench "star_tyre2" (\n, _ => replicate n 'a') (pure . parse a_star2)

    , MkBench "alt_comb" (\n, _ => AltComb.rightGrammar n) (pure . AltComb.run)
    , MkBench "alt_tyre" (\n, _ => rightRE n) (\re => pure $ parse re "a")
    ]

