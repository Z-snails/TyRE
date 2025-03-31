module ConcatTyRE

import Data.Maybe

import TyRE.Core
import TyRE.Parser

export
shape : Nat -> Type
shape 0 = Char
shape (S k) = (Char, shape k)

export
createRE : (n : Nat) -> TyRE (shape n)
createRE 0 = oneOfCharsList ['a']
createRE (S k) = (oneOfCharsList ['a']) <*> (createRE k)
