module Group

import Data.Regex
import Data.Either
import Data.Nat

import Text.Lexer
import Text.Parser.Core
import Text.Parser
import Data.List
import Benchmark
import Data.Regex

import Syntax.PreorderReasoning

data Div2View : Nat -> Type where
  Even : {0 n : Nat} -> (k : Nat) -> {auto 0 ford : n = k + k} -> Div2View n
  Odd : {0 n : Nat} -> (k : Nat) -> {auto 0 ford : n = 1 + k + k} -> Div2View n

div2 : (n : Nat) -> Div2View n
div2 0 = Even 0
div2 (S k) with (div2 k)
  div2 (S (j + j)) | (Even j {ford = Refl}) = Odd j
  div2 (S (S (j + j))) | (Odd j {ford = Refl}) =
    Even (S j) {ford = cong S $ Calc $
                     |~ (1 + j) + j
                     ~~ (j + 1) + j ... cong (+ j) (plusCommutative _ _)
                     ~~ j + (1 + j) ..< plusAssociative _ _ _}

0 btype : (n : Nat) -> Type
btype 0 = ()
btype 1 = ()
btype (S (S k)) with (div2 k)
  btype (S (S k)) | (Even j) = Either (btype (S j)) (btype (S j))
  btype (S (S k)) | (Odd j) = Either (btype (S j)) (btype (S (S j)))

balancedRE : (n : Nat) -> TyRE (btype n)
balancedRE 0 = match 'a'
balancedRE 1 = match 'a'
balancedRE (S (S k)) with (div2 k)
  balancedRE (S (S k)) | (Even j) = balancedRE (S j) <|> balancedRE (S j)
  balancedRE (S (S k)) | (Odd j) = balancedRE (S j) <|> balancedRE (S (S j))

data PToken = AChar

tokenMap : TokenMap PToken
tokenMap = [(is 'a', \x => AChar)]

Rule : Type -> Type
Rule ty = Grammar () PToken True ty

a : Rule ()
a = terminal "a" (\_ => Just ())

rightGrammar : Nat -> Rule Nat
rightGrammar 0 = map (\_ => 1) a
rightGrammar (S k) = map (\_ => 1) a <|> map (+1) (rightGrammar k)

run :
    (rule : Rule Nat) ->
    Either (List1 (ParsingError PToken))
           (Nat, List (WithBounds PToken))
run rule = parse rule (fst (lex tokenMap "a"))

rtype : Nat -> Type
rtype 0 = ()
rtype (S k) = Either () (rtype k)

rightRE : (n : Nat) -> TyRE (rtype n)
rightRE 0 = match 'a'
rightRE (S k) = (match 'a' <|> rightRE k)

export
groupBenchmarks : List Benchmark
groupBenchmarks =
    [ MkBench "group.re_balanced"
        {input = (n : Nat ** TyRE (btype n))}
        (\n, _ => (n ** balancedRE n))
        (\(n ** re) => pure $ ignore $ parse re "a")
    , MkBench "group.re_balanced_group"
        {input = (n : Nat ** TyRE (btype n))}
        (\n, _ => (n ** balancedRE n))
        (\(n ** re) => pure $ ignore $ parse (ignore re) "a")
    , MkBench "group.comb"
        (\n, _ => rightGrammar n)
        (\rule => pure $ run rule)
    , MkBench "group.re_unbalanced"
        {input = (n : Nat ** TyRE (rtype n))}
        (\n, _ => (n ** rightRE n))
        (\(n ** re) => pure $ ignore $ parse re "a")
    , MkBench "group.re_unbalanced_group"
        {input = (n : Nat ** TyRE (rtype n))}
        (\n, _ => (n ** rightRE n))
        (\(n ** re) => pure $ ignore $ parse (ignore re) "a")
    ]
