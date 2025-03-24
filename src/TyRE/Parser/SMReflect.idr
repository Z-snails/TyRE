module TyRE.Parser.SMReflect

import Language.Reflection
import Data.Fin
import Data.SortedSet
import Data.DPair
import Data.SnocList
import Syntax.PreorderReasoning

import TyRE.Parser.SM
import TyRE.Core
import TyRE.Parser.GroupThompson
import TyRE.Extra.Reflects

import Data.Regex

%default total

%language ElabReflection

%hide SM.InitStatesType
%hide SM.TransitionRelation
%hide SM.Instruction

%hide TyRE.DisjointMatches.infix.(::)
%hide TyRE.DisjointMatches.infix.(:<)

mlookup : {0 state : Type} -> (lookup : state -> Type) -> Type -> Maybe state -> Type
mlookup l t Nothing = t
mlookup l t (Just st) = l st

public export
record Thread (0 t : Type) {0 state : Type} (0 lookup : state -> Type) where
    constructor MkThread
    st : Maybe state
    stack : Lazy (mlookup lookup t st)

public export
record CompiledSM (t : Type) where
    constructor MkCompiledSM
    0 state : Type
    0 lookup : state -> Type
    {auto isOrd : Ord state}
    init : List (Thread t lookup)
    next : Thread t lookup -> Char -> List (Thread t lookup)

findAccThread : List (Thread t l) -> Maybe t
findAccThread [] = Nothing
findAccThread (MkThread Nothing x :: _ ) = Just x
findAccThread (_ :: tds) = findAccThread tds

distinct : {0 st : Type} -> Ord st => {0 l : st -> Type} -> List (Thread t l) -> List (Thread t l)
distinct xs = distinctRec xs empty False
  where
    distinctRec : List (Thread t l) -> SortedSet st -> Bool -> List (Thread t l)
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

InitStatesType : (shape : Type) -> (state : Type) -> (state -> Type) -> Type
InitStatesType shape state lookup =
    List (st : Maybe state ** mlookup lookup shape st)

data Instruction : Type -> Type -> Type where
    GetChar : Instruction () Char

    -- Instrutions used by Group
    PushChar : Instruction (SnocList Char) (SnocList Char)
    Pack : Instruction (SnocList Char) String

    PairRight : b -> Instruction a (a, b)
    MapRight : Instruction b c -> Instruction (a, b) (a, c)

    MkLeft : Instruction a (Either a b)
    MkRight : Instruction b (Either a b)

    MkSnoc : Instruction (SnocList a, a) (SnocList a)

    Compose : Instruction a b -> Instruction b c -> Instruction a c
    Id : Instruction a a

    Lift : (a -> b) -> Instruction a b

Interp : Type -> Type -> Type
Interp a b = a -> Char -> b

-- re-functionalised versions of Instruction
-- It seems to help type inference to include these explicitly
export %inline
getChar : Interp () Char
getChar _ c = c

export %inline
pushChar : Interp (SnocList Char) (SnocList Char)
pushChar sx x = sx :< x

export %inline
pack : Interp (SnocList Char) String
pack x c = fastPack $ cast x

export %inline
pairRight : (y : b) -> Interp a (a, b)
pairRight y x c = (x, y)

export %inline
mapRight : Interp b c -> Interp (a, b) (a, c)
mapRight f (x, y) c = (x, f y c)

export %inline
mkLeft : Interp a (Either a b)
mkLeft x c = Left x

export %inline
mkRight : Interp b (Either a b)
mkRight y c = Right y

export %inline
mkSnoc : Interp (SnocList a, a) (SnocList a)
mkSnoc (sx, x) c = sx :< x

export %inline
compose : Interp a b -> Interp b c -> Interp a c
compose f h x c = h (f x c) c

export %inline
instrId : Interp a a
instrId x c = x

0
TransitionRelation : (shape : Type) -> (state : Type) -> (state -> Type) -> Type
TransitionRelation shape state lookup =
    (st1 : state) -> -- source state
    ( CharCond -- the condition for this transition
    , List (st2 : Maybe state ** Instruction (lookup st1) (mlookup lookup shape st2))
    )

-- An alternative formulation of SM
-- which is easier to stage
record ReflectedSM (t : Type) where
    constructor MkReflectedSM
    0 state : Type
    -- The number of non-accepting states
    0 lookup : state -> Type
    {auto isOrd : Ord state}
    -- The list of all states
    enumerate : List state
    -- The set of initial states
    init : InitStatesType t state lookup
    -- The transition function
    next : TransitionRelation t state lookup

splitAccept :
    {0 state, lookup : _} ->
    {0 f : Type -> Type} ->
    List (st : Maybe state ** f (mlookup lookup t st)) ->
    (List (st : state ** f (lookup st)), Maybe (f t))
splitAccept [] = ([], Nothing)
splitAccept ((Nothing ** stk) :: xs) = case splitAccept {f} xs of
    (xs', _) => (xs', Just stk)
splitAccept ((Just st ** stk) :: xs) = case splitAccept {f} xs of
    (xs', ac) => ((st ** stk) :: xs', ac)

public export
compile : {0 a : Type} -> TyRE a -> ReflectedSM a
compile Empty = MkReflectedSM Void absurd [] [(Nothing ** ())] (\st1 => absurd st1)
compile (MatchChar f) =
    let 0 lookup : () -> Type
        lookup () = ()
        init : InitStatesType a () lookup
        init = [(Just () ** ())]
        next : TransitionRelation a () lookup
        next () = (f, [(Nothing ** GetChar)])
        -- next () = (f, [(Nothing ** \_, g, c => (c, g))])
    in MkReflectedSM () lookup [()] init next
compile ((<*>) {a, b} x y) =
    let
        xm = compile x
        ym = compile y

        _ = xm.isOrd
        _ = ym.isOrd

        0 T : Type
        T = Either xm.state ym.state

        0 lookup : T -> Type
        lookup (Left x) = xm.lookup x
        lookup (Right y) = (a, ym.lookup y)

        enumerate = map Left xm.enumerate ++ map Right ym.enumerate

        init : InitStatesType (a, b) T lookup
        init = case splitAccept {f = id} xm.init of
            (xinit, Nothing) => map (\(st ** stk) => (Just (Left st) ** stk)) xinit
            (xinit, Just x) =>
                map (\(st ** stk) => (Just (Left st) ** stk)) xinit
                ++ map (\case
                    (Nothing ** y) => (Nothing ** (x, y))
                    (Just st ** ystk) => (Just (Right st) ** (x, ystk))
                ) ym.init

        next : TransitionRelation (a, b) T lookup
        next (Left x) =
            let (cond, xs) = xm.next x
                xs' = xs >>= \case
                    (Nothing ** upd) => map
                        (\case
                            (Nothing ** y) => (Nothing ** Compose upd (PairRight y))
                            (Just st ** stInit) => (Just (Right st) ** Compose upd (PairRight stInit)))
                        ym.init
                    (Just st1 ** upd) => [(Just (Left st1) ** upd)]
            in (cond, xs')

        next (Right y) =
            let (cond, ys) = ym.next y
            in (cond, map
                (\case
                    (Just y' ** upd) =>
                        (Just (Right y') ** MapRight upd)
                    (Nothing ** upd) =>
                        (Nothing ** MapRight upd))
                ys)

    in MkReflectedSM T lookup enumerate init next
compile ((<|>) {a, b} x y) =
    let xm = compile x
        ym = compile y

        _ = xm.isOrd
        _ = ym.isOrd

        0 T : Type
        T = Either xm.state ym.state

        0 lookup : T -> Type
        lookup (Left x) = xm.lookup x
        lookup (Right y) = ym.lookup y

        enumerate = map Left xm.enumerate ++ map Right ym.enumerate

        init : InitStatesType (Either a b) T lookup
        init =
            let (xinit, xem) = splitAccept {f = id} xm.init
                (yinit, yem) = splitAccept {f = id} ym.init
                -- If both TyREs accept the empty word
                -- then prioritse the one from x
                em = case (xem, yem) of
                    (Just x, _) => [(Nothing ** Left x)]
                    (_, Just y) => [(Nothing ** Right y)]
                    (_, _) => []
            in em
                ++ map (\(st ** stk) => (Just (Left st) ** stk)) xinit
                ++ map (\(st ** stk) => (Just (Right st) ** stk)) yinit

        next : TransitionRelation (Either a b) T lookup
        next (Left x) =
            let (cond, xs) = xm.next x
            in (cond, map (\case
                (Just x' ** upd) => (Just (Left x') ** upd)
                (Nothing ** upd) => (Nothing ** Compose {a = xm.lookup x, b = a, c = Either a b} upd MkLeft)) xs)
        next (Right y) =
            let (cond, ys) = ym.next y
            in (cond, map (\case
                (Just y' ** upd) => (Just (Right y') ** upd)
                (Nothing ** upd) => (Nothing ** Compose upd MkRight)) ys)

    in MkReflectedSM T lookup enumerate init next
compile (Rep {a} x) =
    let xm = compile x
        0 T : Type
        T = xm.state

        _ := xm.isOrd

        0 lookup : T -> Type
        lookup s = (SnocList a, xm.lookup s)

        (xinit, _) := splitAccept {f = id} xm.init

        init : InitStatesType (SnocList a) T lookup
        init = (Nothing ** [<])
            :: map (\(st ** stk) => (Just st ** ([<], stk))) xinit

        next : TransitionRelation (SnocList a) T lookup
        next st1 =
            let (cond, sts) = xm.next st1
            in (cond, sts >>= \case
                (Nothing ** upd) => map
                    (\(st2 ** stk2) => (Just st2 ** Compose (MapRight upd) (Compose MkSnoc (PairRight stk2))))
                    xinit
                (Just st2 ** upd) =>
                    [(Just st2 ** MapRight upd)])

    in MkReflectedSM T lookup xm.enumerate init next
compile (Group r) =
    let MkGroupSM initStates statesWithNext max = groupSM r

        0 T : Type
        T = GroupThompson.State

        0 lookup : T -> Type
        lookup _ = SnocList Char

        enumerate := [0..max - 1]

        init : InitStatesType String T lookup
        init = map
            (\case
                Nothing => (Nothing ** "")
                Just st => (Just (cast st) ** [< ]))
            initStates

        next : TransitionRelation String T lookup
        next st1 = case find (\(st, _) => st1 == cast st) statesWithNext of
            Just (_, MkNextStates cond isSat) =>
                ( cond
                , map
                    (\case
                        Just st => (Just (cast st) ** PushChar)
                        Nothing => (Nothing ** Pack))
                    isSat
                )
            Nothing => (Range ('1', '0'), [])

    in MkReflectedSM T lookup enumerate init next
compile (Conv x f) =
    let xm = compile x
        _ = xm.isOrd
        init : InitStatesType a xm.state xm.lookup
        init = map
            (\case
                (Nothing ** x) => (Nothing ** f x)
                (Just st ** stk) => (Just st ** stk))
            xm.init
        next : TransitionRelation a xm.state xm.lookup
        next st =
            let (cond, xs) = xm.next st
            in (cond, map
                (\case
                    (Nothing ** upd) => (Nothing ** Compose upd (Lift f))
                    (Just st ** upd) => (Just st ** upd))
                xs)
    in MkReflectedSM xm.state xm.lookup xm.enumerate init next

parameters {0 t : Type} (fc : FC) (sm : ReflectedSM t)
    %unbound_implicits off

    mkInit : List (Thread t sm.lookup)
    mkInit = map (\(st ** stk) => MkThread st stk) sm.init

    compInstr : {0 a, b : Type} -> Instruction a b -> Elab TTImp
    compInstr GetChar = pure `(TyRE.Parser.SMReflect.getChar)
    compInstr PushChar = pure `(TyRE.Parser.SMReflect.pushChar)
    compInstr Pack = pure `(TyRE.Parser.SMReflect.pack)
    compInstr (PairRight x) = pure `(TyRE.Parser.SMReflect.pairRight ~(!(quote x)))
    compInstr (MapRight x) = pure `(TyRE.Parser.SMReflect.mapRight ~(!(compInstr x)))
    compInstr MkLeft = pure `(TyRE.Parser.SMReflect.mkLeft)
    compInstr MkRight = pure `(TyRE.Parser.SMReflect.mkRight)
    compInstr MkSnoc = pure `(TyRE.Parser.SMReflect.mkSnoc)
    compInstr (Compose i j) = pure `(TyRE.Parser.SMReflect.compose ~(!(compInstr i)) ~(!(compInstr j)))
    compInstr Id = pure `(TyRE.Parser.SMReflect.instrId)
    compInstr (Lift f) = do
        f <- quote f
        pure `(\x, _ : Char => ~f x)

    list : List TTImp -> TTImp
    list [] = `([])
    list (x :: xs) = `(~x :: ~(list xs))

    genArm : (char : TTImp) -> sm.state -> Elab Clause
    genArm c s = do
        logMsg "tyre" 10 "About to generate arm"
        let sn = sm.next s
        -- failAt fc !(resugarTerm Nothing !(quote sn))
        let (cond, xs) = sm.next s
        sq <- quote s
        logSugaredTerm "tyre" 15 "State" sq
        sat <- quote (satisfies cond)
        let lhs = `(MkThread (Just ~sq) stk)
        logMsg "tyre" 20 "Compiling threads"
        threads <- traverse
            (\(st2 ** upd) => do
                logMsg "tyre" 30 "\tAbout to quote next state"
                st2 <- quote st2
                logSugaredTerm "tyre" 25 "\tCompiling transition to" st2
                upd <- compInstr upd
                logMsg "tyre" 25 "\tCompiled instructions"
                pure `(MkThread ~st2 (Delay (~upd (Force stk) ~c))))
            xs
        logMsg "tyre" 30 "About to list-ify threads"
        let threads = list threads
        logMsg "tyre" 20 "compiled threads"
        let rhs = `(if ~sat ~c then ~threads else [])
        pure $ PatClause fc lhs rhs

    defaultArm : Clause
    defaultArm = PatClause fc `(MkThread _ _) `([])

    genCase : Thread t sm.lookup -> Char -> Elab (List (Thread t sm.lookup))
    genCase td c = do
        td <- quote td
        cq <- quote c
        -- warnAt fc !(resugarTerm Nothing td)
        cls <- traverse (genArm cq) sm.enumerate
        logMsg "tyre" 30 "About to quote case type"
        caseTy <- quote $ Thread t sm.lookup
        logMsg "tyre" 10 "Compiled all arms, about to check case"
        check $ ICase fc [] td caseTy (cls ++ [defaultArm])

    mkNext : Elab (Thread t sm.lookup -> Char -> List (Thread t sm.lookup))
    mkNext = lambda (Thread t sm.lookup) $ \td => lambda Char $ \c => genCase td c

    stage : Elab (CompiledSM t)
    stage = do
        logSugaredTerm "tyre" 20 "About to compile TyRE with next" !(quote sm.next)

        let _ = sm.isOrd
        let init = mkInit
        logMsg "tyre" 5 "About to compile next function"
        next <- mkNext
        logMsg "tyre" 5 "Generated next function"
        pure $ MkCompiledSM sm.state sm.lookup init next

    %unbound_implicits on

doCompile : {0 t : Type} -> TyRE t -> Elab (CompiledSM t)
doCompile re = do
    fc <- getFC <$> quote re
    stage fc (compile re)

bah : CompiledSM String
bah = %runElab doCompile $ Group $ Rep {a=Either Char Char} (MatchChar (Range ('a', 'z')) <|> MatchChar (Range ('g', 'h')))

-- foo : CompiledSM (SnocList (Either () Char))
-- foo = %runElab doCompile $ Rep {a = Either () Char} $ Conv (MatchChar (Range ('a', 'r'))) (\x : Char => ()) <|> MatchChar (Range ('r', 'q'))
foo : CompiledSM String
-- foo = %runElab doCompile $ r "`([01][0-9])`"
-- foo = %runElab doCompile $ Group $ Rep {a = Either () Char} $ Conv (MatchChar (Range ('a', 'r'))) (\x : Char => ()) <|> MatchChar (Range ('r', 'q'))
-- foo = %runElab doCompile (Group (MatchChar (Range ('a', 'z'))))

-- covering
timeRE : TyRE (SnocList (Nat, Nat))
timeRE = Rep $
    Conv
        ( (MatchChar (Range ('0', '1')) <*> MatchChar (Range ('0', '9')))
        `or` (MatchChar (Range ('2', '2')) <*> MatchChar (Range ('0', '3')))
        ) f
    -- <* MatchChar (Range (':', ':'))
    <*> Conv
        (MatchChar (Range ('0', '5')) <*> MatchChar (Range ('0', '9')))
        f
-- timeRE = Rep $
--     map f (r "([01][0-9])!" `or` r "([2][0-3])!")
--     <*> map f (r ":([0-5][0-9])!")
  where
    digit : Char -> Nat
    digit c = cast c `minus` cast '0'

    f : (Char, Char) -> Nat
    f (c1, c2) = 10 * digit c1 + digit c2

%logging "tyre" 100

timeCompiled : CompiledSM (SnocList (Nat, Nat))
timeCompiled = %runElab doCompile timeRE
