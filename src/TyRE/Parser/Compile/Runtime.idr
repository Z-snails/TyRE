module TyRE.Parser.Compile.Runtime

import Data.SortedSet
import Data.SnocList
import public Data.Either

%default total

%language ElabReflection

public export
data Stack : SnocList Type -> Type where
    Lin : Stack [< ]
    (:<) : Stack ts -> t -> Stack (ts :< t)

public export
(++) : Stack as -> Stack bs -> Stack (as ++ bs)
xs ++ Lin = xs
xs ++ (ys :< y) = (xs ++ ys) :< y

public export
mlookup : {0 s : Type} -> (lookup : s -> SnocList Type) -> Type -> Maybe s -> SnocList Type
mlookup l t Nothing = [< t]
mlookup l t (Just st) = l st

public export
record Thread (t : Type) {state : Type} (lookup : state -> SnocList Type) where
    constructor MkThread
    st : Maybe state
    stack : Lazy (Stack (mlookup lookup t st))

public export
record CompiledSM (t : Type) where
    constructor MkCompiledSM
    0 state : Type
    0 lookup : state -> SnocList Type
    {auto isOrd : Ord state}
    init : List (Thread t lookup)
    next : Thread t lookup -> Char -> List (Thread t lookup)

getFromStack : Stack [< t] -> t
getFromStack [< x] = x

findAccThread : List (Thread t l) -> Maybe t
findAccThread [] = Nothing
findAccThread (MkThread Nothing x :: _ ) = Just (getFromStack (Force x))
findAccThread (_ :: tds) = findAccThread tds

distinct : {0 s : Type} -> Ord s => {0 l : s -> SnocList Type} -> List (Thread t l) -> List (Thread t l)
distinct xs = distinctRec xs empty False
  where
    distinctRec : List (Thread t l) -> SortedSet s -> Bool -> List (Thread t l)
    distinctRec [] _ _ = []
    distinctRec (x :: xs) seen seenAcc = case x.st of
        Just s => if contains s seen
            then distinctRec xs seen seenAcc
            else x :: distinctRec xs (insert s seen) seenAcc
        Nothing => if seenAcc
            then distinctRec xs seen seenAcc
            else x :: distinctRec xs seen True

namespace StringRunners
  parameters (sm : CompiledSM t)
    public export
    runTillStrEnd : List Char -> List (Thread t sm.lookup) -> Maybe t
    runTillStrEnd _ [] = Nothing
    runTillStrEnd [] tds = findAccThread tds
    runTillStrEnd (c :: cs) tds =
        runTillStrEnd cs (distinct @{sm.isOrd} $ tds >>= \t => sm.next t c)

    runFromInit : (run : List (Thread t sm.lookup) -> a) -> a
    runFromInit run = run sm.init

    export
    parseFull : List Char -> Maybe t
    parseFull cs = runFromInit (runTillStrEnd cs)

-- re-functionalised versions of Instruction

public export
Interp : SnocList Type -> SnocList Type -> Type
Interp as bs = Stack as -> Char -> Stack bs

export %inline
getChar : Interp pre (pre :< Char)
getChar stk c = stk :< c

export %inline
pushChar : Interp (pre :< SnocList Char) (pre :< SnocList Char)
pushChar (stk :< sx) x = stk :< (sx :< x)

export %inline
pack : Interp (pre :< SnocList Char) (pre :< String)
pack (stk :< xs) _ = stk :< fastPack (cast xs)

export %inline
push : a -> Interp pre (pre :< a)
push x stk _ = stk :< x

export %inline
compose : Interp as bs -> Interp bs cs -> Interp as cs
compose f h x c = h (f x c) c

export %inline
nop : Interp as as
nop x c = x

export %inline
mapTop : (a -> b) -> Interp (pre :< a) (pre :< b)
mapTop f (stk :< x) _ = stk :< f x

export %inline
mkPair : Interp (pre :< a :< b) (pre :< (a, b))
mkPair (stk :< x :< y) _ = stk :< (x, y)

export %inline
mkLeft : Interp (pre :< a) (pre :< Either a b)
mkLeft = mapTop Left

export %inline
mkRight : Interp (pre :< b) (pre :< Either a b)
mkRight = mapTop Right

export %inline
mkSnoc : Interp (pre :< SnocList a :< a) (pre :< SnocList a)
mkSnoc (stk :< sx :< x) _ = stk :< (sx :< x)

public export
DontCompile : Type -> Type
DontCompile ty = ty
