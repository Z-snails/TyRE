module AltComb

import Text.Lexer
import Text.Parser.Core
import Text.Parser
import Data.List

data PToken = AChar

tokenMap : TokenMap PToken
tokenMap = [(is 'a', \x => AChar)]

Rule : Type -> Type
Rule ty = Grammar () PToken True ty

a : Rule ()
a = terminal "a" (\_ => Just ())

export
rightGrammar : Nat -> Rule Nat
rightGrammar 0 = map (\_ => 1) a
rightGrammar (S k) = map (\_ => 1) a <|> map (+1) (rightGrammar k)

export
run : Rule Nat -> Either () ()
run rule = bimap (const ()) (const ()) $
    parse rule (fst (lex tokenMap "a"))
