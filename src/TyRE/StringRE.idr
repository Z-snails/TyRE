module TyRE.StringRE

import Data.SortedSet
import Data.SnocList
import Data.Either
import Data.Vect

import public TyRE.RE
import public TyRE.Core
import public TyRE.Codes

%default total

namespace Raw
    public export
    data RawHoleRE
        = Exactly Char
        | OneOf (List Char)
        | To Char Char
        | Any
        | Hole
        | Concat RawHoleRE RawHoleRE
        | Alt RawHoleRE RawHoleRE
        | Maybe RawHoleRE
        | Group RawHoleRE
        | Rep0 RawHoleRE
        | Rep1 RawHoleRE
        | Keep RawHoleRE

data HoleRE : Nat -> Type where
    Exactly : Char -> HoleRE 0
    OneOf : List Char -> HoleRE 0
    To : Char -> Char -> HoleRE 0
    Any : HoleRE 0
    Hole : HoleRE 1
    Concat : {l : Nat} -> HoleRE l -> HoleRE r -> HoleRE (l + r)
    Alt : {l : Nat} -> HoleRE l -> HoleRE r -> HoleRE (l + r)
    Maybe : HoleRE h -> HoleRE h
    Group : HoleRE h -> HoleRE h
    Rep0 : HoleRE h -> HoleRE h
    Rep1 : HoleRE h -> HoleRE h
    Keep : HoleRE h -> HoleRE h

public export
hole : RawHoleRE -> (h ** HoleRE h)
hole (Exactly c) = (_ ** Exactly c)
hole (OneOf cs) = (_ ** OneOf cs)
hole (To x y) = (_ ** To x y)
hole Any = (_ ** Any)
hole Hole = (_ ** Hole)
hole (Concat l r) =
    let (_ ** l) = hole l
        (_ ** r) = hole r
    in (_ ** Concat l r)
hole (Alt l r) =
    let (_ ** l) = hole l
        (_ ** r) = hole r
    in (_ ** Alt l r)
hole (Maybe x) = let (_ ** x) = hole x in (_ ** Maybe x)
hole (Group x) = let (_ ** x) = hole x in (_ ** Group x)
hole (Rep0 x) = let (_ ** x) = hole x in (_ ** Rep0 x)
hole (Rep1 x) = let (_ ** x) = hole x in (_ ** Rep1 x)
hole (Keep x) = let (_ ** x) = hole x in (_ ** Keep x)

unhole : HoleRE h -> Vect h RE -> RE
unhole (Exactly x) _ = Exactly x
unhole (OneOf xs) _ = OneOf xs
unhole (To x y) _ = To x y
unhole Any _ = Any
unhole Hole [x] = x
unhole (Concat {l} x y) xs =
    let (ls, rs) = splitAt l xs
    in Concat (unhole x ls) (unhole y rs)
unhole (Alt {l} x y) xs =
    let (ls, rs) = splitAt l xs
    in Alt (unhole x ls) (unhole y rs)
unhole (Maybe x) xs = Maybe (unhole x xs)
unhole (Group x) xs = Group (unhole x xs)
unhole (Rep0 x) xs = Rep0 (unhole x xs)
unhole (Rep1 x) xs = Rep1 (unhole x xs)
unhole (Keep x) xs = Keep (unhole x xs)

public export
data Result a = Ok a (List Char) | Err String

public export
Functor Result where
    map f (Ok x cs) = Ok (f x) cs
    map f (Err s) = Err s

private infixl 1 >>>

public export %tcinline
(>>>) : Result a -> (a -> List Char -> Result b) -> Result b
Ok a cs >>> f = f a cs
Err x >>> f = Err x

public export
unexpectedEOI : Result a
unexpectedEOI = Err "Unexpected end of input"

public export
fullRE : List Char -> Result RE

public export
isSpecialChar : Char -> Bool
isSpecialChar c = case c of
    '(' => True; ')' => True
    '[' => True; ']' => True
    '|' => True; '?' => True
    '+' => True; '*' => True
    '.' => True; '!' => True
    _ => False

public export %tcinline
charLit : List Char -> Result Char
charLit [] = unexpectedEOI
charLit ('\\' :: c :: cs) = Ok c cs
charLit (c :: cs) = if isSpecialChar c then Err "Unexpected special character" else Ok c cs

public export
oneOf : List Char -> SnocList Char -> Result (SnocList Char)
oneOf (']' :: cs) acc = Ok acc cs
oneOf [] acc = Err "Unclosed ["
oneOf cs acc = charLit cs >>> \c, cs' => oneOf (assert_smaller cs cs') (acc :< c)

public export
unit : List Char -> Result RE
unit ('.' :: cs) = Ok Any cs
unit ('[' :: a :: '-' :: b :: ']' :: cs) = Ok (To a b) cs
unit ('[' :: cs) = OneOf . cast <$> oneOf cs [<]
unit ('`' :: cs) = fullRE cs >>> \re, cs => case cs of
    '`' :: cs => Ok (Group re) cs
    _ => Err "Unclosed `"
unit ('(' :: cs) = fullRE cs >>> \re, cs => case cs of
    ')' :: cs => Ok re cs
    _ => Err "Unclosed ("
unit cs = Exactly <$> charLit cs

public export
postUnit : Char -> Maybe (RE -> RE)
postUnit '?' = Just Maybe
postUnit '+' = Just Rep1
postUnit '*' = Just Rep0
postUnit '!' = Just Keep
postUnit _ = Nothing

public export
semiUnit : List Char -> Result RE
semiUnit cs = unit cs >>> \x, cs => case cs of
    (c :: cs) => case postUnit c of
        Just f => Ok (f x) cs
        Nothing => Ok x (c :: cs)
    _ => Ok x cs

public export
postSemiUnit : List Char -> Result (RE -> RE)
postSemiUnit ('|' :: cs) = Alt <$> semiUnit cs
postSemiUnit cs = Concat <$> fullRE cs

fullRE cs = semiUnit cs >>> \x, cs' => case postSemiUnit (assert_smaller cs cs') of
    Ok f cs => Ok (f x) cs
    Err e => Ok x cs'

public export
reWithEnd : List Char -> Result RE
reWithEnd cs = fullRE cs >>> \x, cs => case cs of
    [] => Ok x []
    _ => Err "Expected end of input"

public export
rAux : String -> Either String RE
rAux str = case reWithEnd (unpack str) of
    Ok x _ => Right x
    Err x => Left x

public export
fromRight : (x : Either a b) -> {auto 0 isRight : IsRight x} -> b
fromRight (Right x) = x
fromRight (Left x) {isRight = ItIsRight} impossible

public export
toRE : (str : String) -> {auto 0 isRight : IsRight (rAux str)} -> RE
toRE str {isRight} = fromRight (rAux str) @{isRight}

public export
r : (str : String) -> {auto 0 isRight : IsRight (rAux str)} -> TyRE (TypeRE (toRE str {isRight}))
r str {isRight} = compile $ toRE str {isRight}

foo : TyRE Bool
foo = r "(foo)!|(bah)!"
