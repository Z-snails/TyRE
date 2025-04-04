module TyRE.StringRE

import Data.SortedSet
import Data.SnocList
import public Data.Either
import public Data.DPair

import public TyRE.RE
import public TyRE.Core

%default total

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
fullRE : List Char -> Result SomeHoleRE

public export %tcinline
charLit : List Char -> Result Char
charLit [] = Err "Unexpected end of input"
charLit ('\\' :: c :: cs) = Ok c cs
charLit (c :: cs) = if isSpecialChar c then Err "Unexpected special character" else Ok c cs

public export
oneOf : List Char -> SnocList Char -> Result (SnocList Char)
oneOf (']' :: cs) acc = Ok acc cs
oneOf [] acc = Err "Unclosed ["
oneOf cs acc = charLit cs >>> \c, cs' => oneOf (assert_smaller cs cs') (acc :< c)

public export
unit : List Char -> Result SomeHoleRE
unit ('.' :: cs) = Ok (_ ** HMatch Any) cs
unit ('[' :: a :: '-' :: b :: ']' :: cs) = Ok (_ ** HMatch (Range (a, b))) cs
unit ('[' :: cs) = (\cs => (_ ** HMatch $ OneOf (cast cs))) <$> oneOf cs [<]
unit ('`' :: cs) = fullRE cs >>> \(_ ** re), cs => case cs of
    '`' :: cs => Ok (_ ** HGroup re) cs
    _ => Err "Unclosed `"
unit ('(' :: cs) = fullRE cs >>> \(_ ** re), cs => case cs of
    ')' :: cs => Ok (_ ** re) cs
    _ => Err "Unclosed ("
unit ('{' :: '}' :: cs) = Ok (_ ** Hole) cs
unit cs = (\c => (_ ** HExactly c)) <$> charLit cs

public export
postUnit : Char -> Maybe (SomeHoleRE -> SomeHoleRE)
postUnit '?' = Just $ lift HMaybe
postUnit '+' = Just $ lift HRep1
postUnit '*' = Just $ lift HRep0
postUnit '!' = Just $ lift HKeep
postUnit _ = Nothing

public export
semiUnit : List Char -> Result SomeHoleRE
semiUnit cs = unit cs >>> \x, cs => case cs of
    (c :: cs) => case postUnit c of
        Just f => Ok (f x) cs
        Nothing => Ok x (c :: cs)
    _ => Ok x cs

public export
postSemiUnit : List Char -> Result (SomeHoleRE -> SomeHoleRE)
postSemiUnit ('|' :: cs) = flip (lift2 HAlt) <$> semiUnit cs
postSemiUnit cs = flip (lift2 HConcat) <$> fullRE cs

fullRE cs = semiUnit cs >>> \x, cs' => case postSemiUnit (assert_smaller cs cs') of
    Ok f cs => Ok (f x) cs
    Err e => Ok x cs'

public export
reWithEnd : List Char -> Result SomeHoleRE
reWithEnd cs = fullRE cs >>> \x, cs => case cs of
    [] => Ok x []
    _ => Err "Expected end of input"

public export
rAux : String -> Either String SomeHoleRE
rAux str = case reWithEnd (unpack str) of
    Ok x _ => Right x
    Err x => Left x

public export
fromRight : (x : Either a b) -> {auto 0 isRight : IsRight x} -> b
fromRight (Right x) = x
fromRight (Left x) {isRight = ItIsRight} impossible

public export
toRE : (str : String) -> {auto 0 isRight : IsRight (rAux str)} -> SomeHoleRE
toRE str {isRight} = fromRight (rAux str) @{isRight}

public export
rh :
    (str : String) ->
    {auto isRight : IsRight (rAux str)} ->
    (xs : ExistsVect (fst $ toRE str) TyRE) ->
    TyRE (Shape (unhole (snd $ toRE str) xs))
rh str xs = compile $ unhole (snd $ toRE str) xs

public export
r :
    (str : String) ->
    {auto isRight : IsRight (rAux str)} ->
    {auto noHoles : fst (toRE str) = 0} ->
    TyRE (Shape (unholeNone (snd $ toRE str) {noHoles}))
r str = compile $ unholeNone $ snd $ toRE str
