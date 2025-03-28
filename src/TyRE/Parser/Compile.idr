module TyRE.Parser.CompileV2

import Language.Reflection
import Data.Fin
import Data.SortedSet
import Data.DPair
import Data.SnocList
import Syntax.PreorderReasoning

import TyRE.Core
import TyRE.Parser.GroupThompson
import public TyRE.Parser.Compile.Runtime
import TyRE.Extra.Idris
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
    -- The number of states (ie length enumerate)
    size : Integer
    -- Conversion from state to Nat
    toInt : state -> Integer
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
compile Empty = MkReflectedSM Void absurd [] 0 absurd [(Nothing ** [< ()])] (\st1 => absurd st1)
compile (MatchChar f) =
    let 0 lookup : () -> SnocList Type
        lookup () = [<]
        init : InitStatesType a () lookup
        init = [(Just () ** [<])]
        next : TransitionRelation a () lookup
        next () = (f, [(Nothing ** GetChar)])
    in MkReflectedSM () lookup [()] 1 (const 0) init next
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

        enumerate := map Left xm.enumerate ++ map Right ym.enumerate

        toInt : T -> Integer
        toInt (Left x) = xm.toInt x
        toInt (Right y) = xm.size + ym.toInt y

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

    in MkReflectedSM T lookup enumerate (xm.size + ym.size) toInt init next
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

        enumerate := map Left xm.enumerate ++ map Right ym.enumerate

        toInt : T -> Integer
        toInt (Left x) = xm.toInt x
        toInt (Right y) = xm.size + ym.toInt y

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

    in MkReflectedSM T lookup enumerate (xm.size + ym.size) toInt init next
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

    in MkReflectedSM T lookup xm.enumerate xm.size xm.toInt init next
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

    in MkReflectedSM T lookup enumerate max id init next
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
    in MkReflectedSM xm.state xm.lookup xm.enumerate xm.size xm.toInt init next

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

state : TTImp
state = `(Bits32)

asState : Integer -> TTImp
asState i = IPrimVal EmptyFC $ B32 $ cast i

asChar : Char -> TTImp
asChar c = IPrimVal EmptyFC $ Ch c

quoteStack : Stack as -> Elab TTImp
quoteStack [<] = pure `([<])
quoteStack (stk :< x) = (\stk, x => `(~stk :< ~x)) <$> quoteStack stk <*> quote x

parameters {0 t : Type} (sm : ReflectedSM t)
    mkLookup : Elab TTImp
    mkLookup = do
        cs <- for sm.enumerate $ \st =>
            let 0 stk = sm.lookup st
                i = asState $ sm.toInt st
            in quote stk <&> \stk => PatClause EmptyFC i stk
        let cs = cs ++ [PatClause EmptyFC `(_) `([<])]
        let cas = ICase EmptyFC [] `(st) state cs
        pure `(\st => ~cas)

    public export
    mkInit : Elab TTImp
    mkInit = ttimpList <$> traverse
        (\(st ** stk) => do
            let st = ttimpMaybe $ (asState . sm.toInt) <$> st
            logMsg "tyre" 20 "      quote stk"
            stk <- quoteStack stk
            pure `(MkThread ~st ~stk))
        sm.init

    public export
    genArm : TTImp -> sm.state -> Elab Clause
    genArm c s = do
        logMsg "tyre" 20 "      sm.next s"
        let (cond, xs) = sm.next s
        let sq = asState $ sm.toInt s
        logMsg "tyre" 20 "      generate sat"
        sat <- case cond of
            OneOf x => ?todo
            Range (lo, hi) => pure `(~(asChar lo) <= ~c && ~c <= ~(asChar hi))
            Pred f => quote f <&> \f => `(~f ~c)
        let lhs = `(MkThread (Just ~sq) stk)
        logMsg "tyre" 20 "Compiling threads"
        threads <- traverse
            (\(st2 ** upd) => do
                logMsg "tyre" 30 "\tAbout to quote next state"
                let st2 = ttimpMaybe $ (asState . sm.toInt) <$> st2
                logSugaredTerm "tyre" 25 "\tCompiling transition to" st2
                is <- showInstr upd
                logMsg "tyre" 35 "\tCompiling \{is}"
                stk' <- interpQ upd `(Force stk) c
                logMsg "tyre" 25 "\tCompiled instructions"
                pure `(MkThread ~st2 (Delay ~stk')))
            xs
        let threads = ttimpList threads
        let rhs = `(if ~sat then ~threads else [])
        pure $ PatClause EmptyFC lhs rhs

    public export
    defaultArm : Clause
    defaultArm = PatClause EmptyFC `(_) `([])

    public export
    mkNext : Elab TTImp
    mkNext = do
        cls <- traverse (genArm `(c)) sm.enumerate
        let cas = ICase EmptyFC [] `(td) `(_) (cls ++ [defaultArm])
        pure `(\td => \c => ~cas)

    public export
    stage : Elab TTImp
    stage = do
        logMsg "tyre" 5 "    mkLookup"
        lookup <- mkLookup
        logMsg "tyre" 5 "    mkInit"
        init <- mkInit
        logMsg "tyre" 5 "    mkNext"
        next <- mkNext
        pure $ `(MkCompiledSM ~state ~lookup ~init ~next)

asTyRE : TTImp -> Maybe TTImp
asTyRE ty@(IApp _ (IVar _ n) res) = if n == `{TyRE} then Just res else Nothing
asTyRE _ = Nothing

getTyREs : List Decl -> List (Name, TTImp)
getTyREs ds = ds >>= \case
    IClaim claim => case claim.value of
        MkIClaimData _ _ _ (MkTy _ n ty) => case asTyRE ty of
            Just resTy => [(n.value, resTy)]
            Nothing => []
    _ => []

checkTerm : TTImp -> Elab ()
checkTerm t = case doCheck t of
    Left (fc, msg) => failAt fc msg
    Right _ => pure ()
  where
    doCheck : TTImp -> Either (FC, String) ()
    doCheck = ignore . mapMTTImp (\case
        ILocal fc _ _ => Left (fc, "Unable to compile terms with local functions. Make these into top level functions")
        t@(IAlternative _ _ [_]) => Right t
        t@(IAlternative fc _ _) => Left (fc, "Unable to compile terms using some forms of overloading, including (,) syntax for Pair and MkPair")
        t => Right t)

checkClause : Clause -> Elab ()
checkClause (PatClause fc lhs rhs) = checkTerm lhs *> checkTerm rhs
checkClause (WithClause fc lhs rig wval prf flags cls) = ?dfghk
checkClause (ImpossibleClause fc lhs) = checkTerm lhs

checkDecl : Decl -> Elab Decl
checkDecl d@(IClaim x) = do
    let MkIClaimData _ _ _ (MkTy _ _ ty) = x.value
    checkTerm ty
    pure d
checkDecl d@(IData fc x mtreq dt) = ?dfhk_1
checkDecl d@(IDef fc nm cls) = d <$ traverse checkClause cls
checkDecl d@(IParameters fc params decls) = d <$ assert_total (traverse checkDecl decls)
checkDecl d@(IRecord fc mstr x mtreq rec) = ?dfhk_4
checkDecl d@(INamespace fc ns decls) = d <$ assert_total (traverse checkDecl decls)
checkDecl d@(ITransform fc nm s t) = ?dfhk_6
checkDecl d@(IRunElabDecl fc s) = ?dfhk_7
checkDecl d@(ILog x) = ?dfhk_8
checkDecl d@(IBuiltin fc bty nm) = ?dfhk_9

rewriteDecl : (tmpNS, genNS : Namespace) -> List (Name, TTImp) -> Decl -> Elab Decl
rewriteDecl tmpNS genNS resTys d@(IClaim x) = do
    let MkIClaimData count vis opts (MkTy fc n ty) = x.value
    case asTyRE ty of
        Just resTy =>
            let ty = `(CompiledSM ~resTy)
            in pure $ IClaim $
                MkFCVal x.fc (MkIClaimData count vis opts (MkTy fc n ty))
        Nothing => pure d
rewriteDecl tmpNS genNS resTys d@(IDef fc n _) = case lookup n resTys of
    Just resTy => do
        logMsg "tyre" 5 "Compiling TyRE: \{show n}"
        res <- check {expected = Type} resTy
        val <- check {expected = TyRE res} $ IVar EmptyFC $ NS tmpNS n
        logMsg "tyre" 5 "  About to compile"
        let re = compile val
        logMsg "tyre" 5 "  About to stage"
        staged <- stage re
        logMsg "tyre" 5 "  Replacing tmp namespace"
        let staged = replaceNs tmpNS genNS staged
        pure $ IDef fc n [PatClause fc (IVar EmptyFC n) staged]
    Nothing => pure d
rewriteDecl tmpNS genNS resTys d = pure d

defaultImports : List ModuleIdent
defaultImports = [`{TyRE.Parser.Compile.Runtime}]

export covering
createTyREMod : Name -> List Decl -> Elab ()
createTyREMod n ds = do
    logMsg "tyre" 5 "Starting"

    let Just mi = nameAsMod n
        | Nothing => fail "Invalid module ident: \{show n}"
    let relTmpNS = case mi of
            MkMI parts => MkNS ("_hidden" :: parts)
    let genNS = modAsNamespace mi
    thisNS <- currentNS
    let absTmpNS = thisNS ++ relTmpNS

    -- Declare all functions in a hidden namespace
    -- to ensure they typecheck and also so we can
    -- reference the TyREs. We only need to export TyREs
    declare
        [ INamespace EmptyFC relTmpNS
            (map (changeVis $ \case
                Just ty => case asTyRE ty of { Just _ => Export; Nothing => Private }
                Nothing => Private)
                ds)
        ]

    let resTys = getTyREs ds

    ds' <- traverse (rewriteDecl absTmpNS genNS resTys >=> checkDecl) ds

    let imports = map (\n => MkImport False n Nothing) defaultImports

    writeIfChanged "TyRE" SourceDir (modIdentAsPath mi) (prettyModule mi imports ds')

    logMsg "tyre" 5 "Done"

doCompile : TyRE t -> Elab (CompiledSM t)
doCompile re = stage (compile re) >>= check

%logging "tyre" 100

%runElab createTyREMod `{Generated} `[
    foo : Char -> Int
    foo c = ord c - 10

    export
    bah : TyRE Int
    bah = Conv (MatchChar (Range ('a', 'z'))) foo

    bah2 : TyRE String
    bah2 = Group $ Rep {a = Either Char (Char, Char)} (MatchChar (Range ('a', 'z')) <|> (MatchChar (Range ('g', 'h')) <*> MatchChar (Range ('i', 'j'))))

    digit : Char -> Nat
    digit c = cast c `minus` cast '0'

    f : Pair Char Char -> Nat
    f (MkPair c1 c2) = 10 * digit c1 + digit c2

    export
    timeRE : TyRE (SnocList (Pair Nat Nat))
    timeRE = Rep $
        Conv
            ( (MatchChar (Range ('0', '1')) <*> MatchChar (Range ('0', '9')))
            `or` (MatchChar (Range ('2', '2')) <*> MatchChar (Range ('0', '3')))
            ) f
        <* MatchChar (Range (':', ':'))
        <*> Conv
            (MatchChar (Range ('0', '5')) <*> MatchChar (Range ('0', '9')))
            f
]
