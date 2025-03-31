module StarComb

import Text.Lexer
import public Text.Parser.Core
import public Text.Parser

data AToken = AChar | EndTok

tokenMap : TokenMap AToken
tokenMap = [(is 'a', \x => AChar),
            (is '$', \x => EndTok)]

Rule : Type -> Type
Rule ty = Grammar () AToken True ty

a : Rule Char
a = terminal "a" (\tok => case tok of {AChar => Just 'a'; EndTok => Nothing})

eoi : Rule ()
eoi = terminal "end" (\tok => case tok of {AChar => Nothing; EndTok => Just ()})

export
grammar : Rule (List Char)
grammar = manyTill eoi a

export
run :
    String ->
    Either () ()
run inp = bimap (const ()) (const ()) $
    parse grammar (fst (lex tokenMap (inp ++ "$")))
