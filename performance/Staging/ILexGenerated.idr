module Staging.ILexGenerated
import public Text.ILex.Util
%default total

public export
lexRepA : String -> Either LexErr (SnocList Unit)

public export
lexRepA1 : List Char -> Either LexErr (SnocList Unit)

public export
lexRepA2 : List Char -> SnocList Unit -> Either LexErr (SnocList Unit)

public export
lexRepA3 : List Char -> SnocList Unit -> Either LexErr (SnocList Unit)

lexRepA = lexRepA1 . unpack

lexRepA1 str = lexRepA2 str Lin
lexRepA2 str@(c::cs) x0 =
  case c of
    'a' => lexRepA2 cs ((:<) x0 MkUnit)
    _   => lexRepA3 str x0
lexRepA2 [] x0 = lexRepA3 Nil x0

lexRepA3 str@(c::cs) x0 = Left (Unexpected c)
lexRepA3 [] x0 = Right x0



public export
lexTimes : String -> Either LexErr (SnocList (Pair Nat Nat))

public export
lexTimes1 : List Char -> Either LexErr (SnocList (Pair Nat Nat))

public export
lexTimes2 : List Char -> SnocList (Pair Nat Nat) -> Either LexErr (SnocList (Pair Nat Nat))

public export
lexTimes3 : List Char -> SnocList (Pair Nat Nat) -> Either LexErr (SnocList (Pair Nat Nat))

public export
lexTimes4 : List Char -> Char -> SnocList (Pair Nat Nat) -> Either LexErr (SnocList (Pair Nat Nat))

public export
lexTimes5 : List Char -> Char -> SnocList (Pair Nat Nat) -> Either LexErr (SnocList (Pair Nat Nat))

public export
lexTimes6 : List Char -> Nat -> SnocList (Pair Nat Nat) -> Either LexErr (SnocList (Pair Nat Nat))

public export
lexTimes7 : List Char -> Nat -> Char -> SnocList (Pair Nat Nat) -> Either LexErr (SnocList (Pair Nat Nat))

lexTimes = lexTimes1 . unpack

lexTimes1 str = lexTimes2 str Lin
lexTimes2 str@(c::cs) x0 =
  case c of
    '2' => lexTimes4 cs c x0
    _  => case (&&) ((<=) c '1') ((<=) '0' c) of
      True => lexTimes5 cs c x0
      _   => lexTimes3 str x0
lexTimes2 [] x0 = lexTimes3 Nil x0

lexTimes3 str@(c::cs) x0 = Left (Unexpected c)
lexTimes3 [] x0 = Right x0

lexTimes4 str@(c::cs) x1 x0 =
  case (&&) ((<=) c '3') ((<=) '0' c) of
    True => lexTimes6 cs ((+) ((*) (fromInteger 10) (cast (toDigit x1))) (cast (toDigit c))) x0
    _    => Left (cast (Unexpected c))
lexTimes4 [] x1 x0 = Left (cast EOI)

lexTimes5 str@(c::cs) x1 x0 =
  case (&&) ((<=) c '9') ((<=) '0' c) of
    True => lexTimes6 cs ((+) ((*) (fromInteger 10) (cast (toDigit x1))) (cast (toDigit c))) x0
    _    => Left (cast (Unexpected c))
lexTimes5 [] x1 x0 = Left (cast EOI)

lexTimes6 str@(c::cs) x1 x0 =
  case (&&) ((<=) c '5') ((<=) '0' c) of
    True => lexTimes7 cs x1 c x0
    _    => Left (cast (Unexpected c))
lexTimes6 [] x1 x0 = Left (cast EOI)

lexTimes7 str@(c::cs) x2 x1 x0 =
  case (&&) ((<=) c '9') ((<=) '0' c) of
    True => lexTimes2 cs ((:<) x0 (MkPair x2 ((+) ((*) (fromInteger 10) (cast (toDigit x1))) (cast (toDigit c)))))
    _    => Left (cast (Unexpected c))
lexTimes7 [] x2 x1 x0 = Left (cast EOI)


