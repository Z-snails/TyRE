module ConcatComb

import Text.Lexer
import Text.Parser.Core
import Text.Parser
import Data.List

data AToken = AChar

aTokenMap : TokenMap AToken
aTokenMap = [(is 'a', \x => AChar)]

Rule : Type -> Type
Rule ty = Grammar () AToken True ty

gType : Nat -> Type
gType 0 = Char
gType (S k) = (Char, gType k)

justAGrammar : Rule Char
justAGrammar = terminal "a" (\tok => Just 'a')

getGrammar : (n : Nat) -> Rule (gType n)
getGrammar 0 = justAGrammar
getGrammar (S k) = (map MkPair justAGrammar <*> getGrammar k)

resToStr  : {auto showChar : Show Char }
          -> {auto showEither : ({a,b : Type} -> (Show a, Show b) => Show (a, b))}
          -> (n: Nat) -> Show (gType n)
resToStr 0 = showChar
resToStr (S k) =
  let _ := resToStr k
  in showEither

export
Input : Type
Input = (n : Nat ** (Rule (gType n), String))

export
getInput : Nat -> Maybe Input -> Input
getInput n (Just (_ ** (_, cs))) = (n ** (getGrammar n, "a" ++ cs))
getInput n _ = (n ** (getGrammar n, fastPack $ replicate n 'a'))

export
run : Input -> Either () ()
run (n ** (rule, inp)) = bimap (const ()) (const ()) $
    parse rule (fst (lex aTokenMap inp))
