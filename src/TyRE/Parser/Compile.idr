module TyRE.Parser.Compile

import Language.Reflection
import Data.Fin
import Data.SortedSet
import Data.DPair
import Data.SnocList
import Syntax.PreorderReasoning

import TyRE.Core
import TyRE.Parser.GroupThompson
import public TyRE.Parser.Compile.Runtime
import TyRE.Extra.Elab

import Data.Regex

%default total

%language ElabReflection

%hide TyRE.DisjointMatches.infix.(::)
%hide TyRE.DisjointMatches.infix.(:<)

data Instruction : SnocList Type -> SnocList Type -> Type where
    GetChar : Instruction pre (pre :< Char)

    -- Instrutions used by Group
    PushChar : Instruction (pre :< SnocList Char) (pre :< SnocList Char)
    Pack : Instruction (pre :< SnocList Char) (pre :< String)

    -- General stack machine instructions
    Push : b -> Instruction pre (pre :< b)
    Then : Instruction as bs -> Instruction bs cs -> Instruction as cs

    -- Constructors for data
    MkPair : Instruction (pre :< a :< b) (pre :< (a, b))
    MkLeft : Instruction (pre :< a) (pre :< Either a b)
    MkRight : Instruction (pre :< b) (pre :< Either a b)
    MkSnoc : Instruction (pre :< SnocList a :< a) (pre :< SnocList a)

    -- Lift a function to operate on the stack
    MapTop : (a -> b) -> Instruction (pre :< a) (pre :< b)

-- data Routine : SnocList Type -> SnocList Type -> Type where
--     Nop : Routine as as
--     Then : Routine as bs -> Instruction bs cs -> Routine as cs

private infixl 7 `Then`

-- namespace Instruction
export
lift : Instruction as bs -> Instruction (pre ++ as) (pre ++ bs)
lift GetChar = GetChar
lift PushChar = PushChar
lift Pack = Pack
lift (Push x) = Push x
lift (i `Then` j) = lift i `Then` lift j
lift MkPair = MkPair
lift MkLeft = MkLeft
lift MkRight = MkRight
lift MkSnoc = MkSnoc
lift (MapTop f) = MapTop f

-- namespace Routine
--     export
--     lift : Routine as bs -> Routine (pre ++ as) (pre ++ bs)
--     lift Nop = Nop
--     lift (is `Then` i) = lift is `Then` lift i

--     export
--     (++) : Routine as bs -> Routine bs cs -> Routine as cs
--     is ++ Nop = is
--     is ++ (js `Then` j) = (is ++ js) `Then` j

-- thenPushAll : Routine as bs -> Stack cs -> Routine as (bs ++ cs)
-- thenPushAll r [<] = r
-- thenPushAll r (xs :< x) = (r `thenPushAll` xs) `Then` Push x

thenPushAll : Instruction as bs -> Stack cs -> Instruction as (bs ++ cs)
thenPushAll r [<] = r
thenPushAll r (xs :< x) = (r `thenPushAll` xs) `Then` Push x

InitStatesType : (shape : Type) -> (state : Type) -> (state -> SnocList Type) -> Type
InitStatesType shape state lookup =
    List (st : Maybe state ** Stack (mlookup lookup shape st))

0
TransitionRelation : (shape : Type) -> (state : Type) -> (state -> SnocList Type) -> Type
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
    0 lookup : state -> SnocList Type
    {auto isOrd : Ord state}
    -- The list of all states
    enumerate : List state
    -- The set of initial states
    init : InitStatesType t state lookup
    -- The transition function
    next : TransitionRelation t state lookup

public export
splitAccept :
    {0 state, lookup : _} ->
    {0 f : SnocList Type -> Type} ->
    List (st : Maybe state ** f (mlookup lookup t st)) ->
    (List (st : state ** f (lookup st)), Maybe (f [< t]))
splitAccept [] = ([], Nothing)
splitAccept ((Nothing ** stk) :: xs) = case splitAccept {f} xs of
    (xs', _) => (xs', Just stk)
splitAccept ((Just st ** stk) :: xs) = case splitAccept {f} xs of
    (xs', ac) => ((st ** stk) :: xs', ac)

public export
compile : {0 a : Type} -> TyRE a -> ReflectedSM a
compile Empty = MkReflectedSM Void absurd [] [(Nothing ** [< ()])] (\st1 => absurd st1)
compile (MatchChar f) =
    let 0 lookup : () -> SnocList Type
        lookup () = [<]
        init : InitStatesType a () lookup
        init = [(Just () ** [<])]
        next : TransitionRelation a () lookup
        next () = (f, [(Nothing ** GetChar)])
    in MkReflectedSM () lookup [()] init next
compile ((<*>) {a, b} x y) =
    let
        xm = compile x
        ym = compile y

        _ = xm.isOrd
        _ = ym.isOrd

        0 T : Type
        T = Either xm.state ym.state

        0 lookup : T -> SnocList Type
        lookup (Left x) = xm.lookup x
        lookup (Right y) = [< a] ++ ym.lookup y

        enumerate = map Left xm.enumerate ++ map Right ym.enumerate

        init : InitStatesType (a, b) T lookup
        init = case splitAccept {f = Stack} xm.init of
            (xinit, Nothing) => map (\(st ** stk) => (Just (Left st) ** stk)) xinit
            (xinit, Just x) =>
                map (\(st ** stk) => (Just (Left st) ** stk)) xinit
                ++ map (\case
                    (Nothing ** y) => (Nothing ** case (x, y) of { ([< x], [< y]) => [< (x, y)] })
                    (Just st ** ystk) => (Just (Right st) ** (x ++ ystk))
                ) ym.init

        next : TransitionRelation (a, b) T lookup
        next (Left x) =
            let (cond, xs) = xm.next x
                xs' = xs >>= \case
                    (Nothing ** upd) => map
                        (\case
                            (Nothing ** [< y]) => (Nothing ** upd `Then` Push y `Then` MkPair)
                            (Just st ** stInit) => (Just (Right st) ** upd `thenPushAll` stInit))
                        ym.init
                    (Just st2 ** upd) => [(Just (Left st2) ** upd)]
            in (cond, xs')

        next (Right y) =
            let (cond, ys) = ym.next y
            in (cond, map
                (\case
                    (Just y' ** upd) =>
                        (Just (Right y') ** lift upd)
                    (Nothing ** upd) =>
                        (Nothing ** lift upd `Then` MkPair))
                ys)

    in MkReflectedSM T lookup enumerate init next
compile ((<|>) {a, b} x y) =
    let xm = compile x
        ym = compile y

        _ = xm.isOrd
        _ = ym.isOrd

        0 T : Type
        T = Either xm.state ym.state

        0 lookup : T -> SnocList Type
        lookup (Left x) = xm.lookup x
        lookup (Right y) = ym.lookup y

        enumerate = map Left xm.enumerate ++ map Right ym.enumerate

        init : InitStatesType (Either a b) T lookup
        init =
            let (xinit, xem) = splitAccept {f = Stack} xm.init
                (yinit, yem) = splitAccept {f = Stack} ym.init
                -- If both TyREs accept the empty word
                -- then prioritse the one from x
                em = case (xem, yem) of
                    (Just [< x], _) => [(Nothing ** [< Left x])]
                    (_, Just [< y]) => [(Nothing ** [< Right y])]
                    (_, _) => []
            in em
                ++ map (\(st ** stk) => (Just (Left st) ** stk)) xinit
                ++ map (\(st ** stk) => (Just (Right st) ** stk)) yinit

        next : TransitionRelation (Either a b) T lookup
        next (Left x) =
            let (cond, xs) = xm.next x
            in (cond, map
                (\case
                    (Just x' ** upd) => (Just (Left x') ** upd)
                    (Nothing ** upd) => (Nothing ** upd `Then` MkLeft))
                xs)
        next (Right y) =
            let (cond, ys) = ym.next y
            in (cond, map
                (\case
                    (Just y' ** upd) => (Just (Right y') ** upd)
                    (Nothing ** upd) => (Nothing ** upd `Then` MkRight))
                ys)

    in MkReflectedSM T lookup enumerate init next
compile (Rep {a} x) =
    let xm = compile x
        0 T : Type
        T = xm.state

        _ := xm.isOrd

        0 lookup : T -> SnocList Type
        lookup s = [< SnocList a] ++ xm.lookup s

        (xinit, _) := splitAccept {f = Stack} xm.init

        init : InitStatesType (SnocList a) T lookup
        init = (Nothing ** [< [<]])
            :: map (\(st ** stk) => (Just st ** [< Prelude.Lin] ++ stk)) xinit

        next : TransitionRelation (SnocList a) T lookup
        next st1 =
            let (cond, sts) = xm.next st1
            in (cond, sts >>= \case
                (Nothing ** upd) => map
                    (\(st2 ** stk2) => (Just st2 ** (lift upd `Then` MkSnoc) `thenPushAll` stk2))
                    xinit
                (Just st2 ** upd) =>
                    [(Just st2 ** lift upd)])

    in MkReflectedSM T lookup xm.enumerate init next
compile (Group r) =
    let MkGroupSM initStates statesWithNext max = groupSM r

        0 T : Type
        T = GroupThompson.State

        0 lookup : T -> SnocList Type
        lookup _ = [< SnocList Char]

        enumerate := [0..max - 1]

        init : InitStatesType String T lookup
        init = map
            (\case
                Nothing => (Nothing ** [< ""])
                Just st => (Just (cast st) ** [< Prelude.Lin]))
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
compile {a = b} (Conv x f) =
    let xm = compile x
        _ = xm.isOrd
        init : InitStatesType b xm.state xm.lookup
        init = map
            (\case
                (Nothing ** [< x]) => (Nothing ** [< f x])
                (Just st ** stk) => (Just st ** stk))
            xm.init
        next : TransitionRelation b xm.state xm.lookup
        next st =
            let (cond, xs) = xm.next st
            in (cond, map
                (\case
                    (Nothing ** upd) => (Nothing ** upd `Then` MapTop f)
                    (Just st ** upd) => (Just st ** upd))
                xs)
    in MkReflectedSM xm.state xm.lookup xm.enumerate init next

-- optInstr : {0 as, bs : SnocList Type} -> Routine as bs -> Routine as bs
-- optInstr
-- optInstr (Compose x y) = case (optInstr x, optInstr y) of
--     (Nop, y') => y'
--     (x', Nop) => x'
--     (x', y') => Compose x' y'
-- optInstr x = x

-- %inline
interp : (i : Instruction as bs) -> Interp as bs
interp GetChar = getChar
interp PushChar = pushChar
interp Pack = pack
interp (Push x) = push x
interp (i `Then` j) = compose (interp i) (interp j)
interp MkPair = mkPair
interp MkLeft = mkLeft
interp MkRight = mkRight
interp MkSnoc = mkSnoc
interp (MapTop f) = mapTop f

interpQ : Instruction as bs -> (stk : TTImp) -> (c : TTImp) -> Elab TTImp
interpQ GetChar stk c = pure `(~stk :< ~c)
interpQ PushChar stk c = pure `(pushChar ~stk ~c)
interpQ Pack stk c = pure `(pack ~stk ~c)
interpQ (Push x) stk c = quote x <&> \x => `(~stk :< ~x)
interpQ (x `Then` y) stk c = do
    stk' <- interpQ x stk c
    interpQ y stk' c
interpQ MkPair stk c = pure `(mkPair ~stk ~c)
interpQ MkLeft stk c = pure `(mkLeft ~stk ~c)
interpQ MkRight stk c = pure `(mkRight ~stk ~c)
interpQ MkSnoc stk c = pure `(mkSnoc ~stk ~c)
interpQ (MapTop f) stk c = quote f <&> \f => `(mapTop ~f ~stk ~c)

showInstr : Instruction as bs -> Elab String
showInstr GetChar = pure "GetChar"
showInstr PushChar = pure "PushChar"
showInstr Pack = pure "Pack"
showInstr (Push x) = pure "Push"
showInstr (x `Then` y) =
    (\x, y => "\{x} \{y}")
        <$> showInstr x
        <*> showInstr y
showInstr MkPair = pure "MkPair"
showInstr MkLeft = pure "MkLeft"
showInstr MkRight = pure "MkRight"
showInstr MkSnoc = pure "MkSnoc"
showInstr (MapTop f) = pure "MapTop"

parameters {0 t : Type} (sm : ReflectedSM t)
    public export
    mkInit : List (Thread t sm.lookup)
    mkInit = map (\(st ** stk) => MkThread st stk) sm.init

    public export
    list : List TTImp -> TTImp
    list [] = `([])
    list (x :: xs) = `(~x :: ~(list xs))

    public export
    genArm : TTImp -> sm.state -> Elab Clause
    genArm c s = do
        logMsg "tyre" 10 "About to generate arm"
        let sn = sm.next s
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
                is <- showInstr upd
                -- logSugaredTerm "tyre" 35 "\tInstructions" upd
                logMsg "tyre" 35 "\tCompiling \{is}"
                -- upd <- quote (interp upd)
                stk' <- interpQ upd `(Force stk) c
                -- upd <- quote upd
                -- upd <- quote (interpR upd)
                logMsg "tyre" 25 "\tCompiled instructions"
                -- pure `(MkThread ~st2 (Delay (interp ~upd (Force stk) ~c))))
                pure `(MkThread ~st2 (Delay ~stk')))
            xs
        let threads = list threads
        logMsg "tyre" 20 "compiled threads"
        let rhs = `(if ~sat ~c then ~threads else [])
        pure $ PatClause EmptyFC lhs rhs

    public export
    defaultArm : Clause
    defaultArm = PatClause EmptyFC `(_) `([])

    public export
    genCase : TTImp -> TTImp -> Elab (List (Thread t sm.lookup))
    genCase td c = do
        cls <- traverse (genArm c) sm.enumerate
        logMsg "tyre" 30 "About to quote case type"
        caseTy <- quote (Thread t sm.lookup)
        logMsg "tyre" 10 "Compiled all arms, about to check case"
        check $ ICase EmptyFC [] td caseTy (cls ++ [defaultArm])

    public export
    mkNext : Elab (Thread t sm.lookup -> Char -> List (Thread t sm.lookup))
    mkNext = lambda (Thread t sm.lookup) $ \td => lambda Char $ \c => do
        td <- quote td
        c <- quote c
        genCase td c

    public export
    stage : Elab (CompiledSM t)
    stage = do
        -- logSugaredTerm "tyre" 20 "About to compile TyRE with next" !(quote sm.next)
        let _ = sm.isOrd
        logMsg "tyre" 5 "About to compile next function"
        next <- mkNext
        logMsg "tyre" 5 "Generated next function"
        pure $ MkCompiledSM sm.state sm.lookup mkInit next

export
doCompile : {0 t : Type} -> TyRE t -> Elab (CompiledSM t)
doCompile re = do
    -- qre <- quote re
    stage (compile re)


%logging "tyre" 100

bah : CompiledSM String
-- bah = %runElab doCompile $ Group $ Rep {a=Either Char Char} (MatchChar (Range ('a', 'z')) <|> MatchChar (Range ('g', 'h')))

-- foo : CompiledSM (SnocList (Either () Char))
-- foo = %runElab doCompile $ Rep {a = Either () Char} $ Conv (MatchChar (Range ('a', 'r'))) (\x : Char => ()) <|> MatchChar (Range ('r', 'q'))
foo : CompiledSM String
-- foo = %runElab doCompile $ r "`([01][0-9])`"
-- foo = %runElab doCompile $ Group $ Rep {a = Either () Char} $ Conv (MatchChar (Range ('a', 'r'))) (\x : Char => ()) <|> MatchChar (Range ('r', 'q'))
-- foo = %runElab doCompile (Group (Rep $ MatchChar (Range ('a', 'z'))))
-- foo = %runElab doCompile (Group (MatchChar (Range ('a', 'z'))) `Conv` id)
-- foo = %runElab doCompile (Group (MatchChar (Range ('a', 'z')) <*> MatchChar (Range ('a', 'z'))))

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

export
timeCompiled : CompiledSM (SnocList (Nat, Nat))
-- timeCompiled = %runElab doCompile timeRE

-- Compiles here
simple : CompiledSM Unit
simple = %runElab doCompile Empty


