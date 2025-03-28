-- Pretty printer for TTImp that aims to generate valid Idris code
-- TODO: make this a separate package at some point?
module TyRE.Extra.Idris

import Language.Reflection
import Data.Maybe

isEmptyFC : FC -> Bool
isEmptyFC EmptyFC = True
isEmptyFC _ = False

Show ModuleIdent where
    show (MkMI strs) = showSep "." $ reverse strs

Show OriginDesc where
    show (PhysicalIdrSrc ident) = show ident
    show (PhysicalPkgSrc fname) = fname
    show (Virtual Interactive) = "repl"

-- Show

showPos : FilePos -> String
showPos (l, c) = "\{show l}:\{show c}"

Show FC where
    show (MkFC origin start end) = "\{show origin}:\{showPos start}--\{showPos end}"
    show (MkVirtualFC origin start end) = "\{show origin}:\{showPos start}--\{showPos end}"
    show EmptyFC = "EmptyFC"

isImplicit : TTImp -> Bool
isImplicit (Implicit _ _) = True
isImplicit _ = False

data Pos = Open | Fun | Arg

posIdx : Pos -> Bits8
posIdx Open = 0
posIdx Fun = 1
posIdx Arg = 2

Eq Pos where
    x == y = posIdx x == posIdx y

Ord Pos where
    compare x y = compare (posIdx x) (posIdx y)

showName : Name -> String
showName n@(NS _ _) = showPrefix True n
showName n@(UN _) = showPrefix True n
showName (MN str i) = "mn_\{show i}_\{str}"
showName (DN str nm) = showName nm
showName (Nested (x, y) nm) = "n_\{show x}_\{show y}_\{showName nm}"
showName (CaseBlock str i) = "case_{\show i}_\{str}"
showName (WithBlock str i) = "with_{\show i}_\{str}"

data Argument
    = Positional TTImp
    | Named Name TTImp
    | Auto TTImp
    | With TTImp

asApp : (f : TTImp) -> List Argument -> (TTImp, List Argument)
asApp (IApp _ f x) acc = asApp f (Positional x :: acc)
asApp (INamedApp _ f n x) acc = asApp f (Named n x :: acc)
asApp (IAutoApp _ f x) acc = asApp f (Auto x :: acc)
asApp (IWithApp _ f x) acc = asApp f (With x :: acc)
asApp f acc = (f, acc)

keepArg : Argument -> Bool
keepArg (Named n (IHole _ n')) = False
keepArg (Named n x) = not $ isOp n
keepArg _ = True

prettyOpts : List FnOpt -> String -> String
prettyOpts [] s = s
prettyOpts (o :: os) s =
    let o = case o of
            Inline => "%inline "
            NoInline => "%noinline "
            Deprecate => "%deprecate "
            TCInline => "%tcinline "
            (Hint normal) => if normal then "%hint " else "%chaser "
            (GlobalHint normal) => if normal then "%globalhint " else "%defaulthint "
            ExternFn => "%extern"
            (ForeignFn ss) => ?dfghjk_7
            (ForeignExport ss) => ?dfghjk_8
            Invertible => ?dfghjk_9
            (Totality treq) => "%\{show treq} "
            Macro => "%macro "
            (SpecArgs nms) => ?dfghjk_12
    in o ++ prettyOpts os s

prettyTm : Pos -> TTImp -> String
prettyClause : String -> Clause -> String
prettyDecl : (local : Bool) -> (indent : String) -> Decl -> String

prettyApp : Pos -> TTImp -> String
prettyApp p t =
    let (f, xs) = asApp t []
        xs = filter keepArg xs
    in showParens (p > Fun) $ showSep " " $ prettyTm Fun f :: map prettyArgument xs
  where
    prettyArgument : Argument -> String
    prettyArgument (Positional s) = prettyTm Arg s
    prettyArgument (Named nm s) = "{\{showName nm} = \{prettyTm Open s}}"
    prettyArgument (Auto s) = "@{\{prettyTm Open s}}"
    prettyArgument (With s) = ?with_app

prettyTm p (IVar fc nm) = showName nm
prettyTm p (IPi fc rig pinfo mnm argTy retTy) =
    let n = maybe "_" showName mnm
    in showParens (p > Fun) $ case pinfo of
        ImplicitArg => "{\{showCount rig n} : \{prettyTm Open argTy}} -> \{prettyTm Fun retTy}"
        ExplicitArg => "(\{showCount rig n} : \{prettyTm Open argTy}) -> \{prettyTm Fun retTy}"
        AutoImplicit => "{auto \{showCount rig n} : \{prettyTm Open argTy} -> \{prettyTm Fun retTy}"
        (DefImplicit x) => "{default \{prettyTm Arg x} \{showCount rig n} : \{prettyTm Open argTy} -> \{prettyTm Fun retTy}"
prettyTm p (ILam fc rig pinfo mnm argTy scope) =
    let n = maybe "_" showName mnm
    in showParens (p > Open) "\\ \{n} => \{prettyTm Open scope}"
prettyTm p (ILet fc lhsFC rig nm nTy nVal scope) = ?dfghkj_3
prettyTm p (ICase fc xs s ty cls) =
    let cls = showSep " ; " $ map (prettyClause "=>") cls
        scr = prettyTm Open s
        -- scr = if isImplicit ty
        --     then prettyTm Open s
        --     else "the \{prettyTm Arg ty} \{prettyTm Arg s}"
    in showParens (p > Open) "case \{scr} of { \{cls} }"
prettyTm p (ILocal fc decls s) =
    let bind = showSep "; " $ map (prettyDecl True "") decls
    in "let \{bind} in \{prettyTm Open s}"
prettyTm p (IUpdate fc upds s) = ?dfghkj_6
prettyTm p t@(IApp _ _ _) = prettyApp p t
prettyTm p t@(INamedApp _ _ _ _) = prettyApp p t
prettyTm p t@(IAutoApp _ _ _) = prettyApp p t
prettyTm p t@(IWithApp _ _ _) = prettyApp p t
prettyTm p (ISearch fc depth) = ?dfgk
prettyTm p (IAlternative fc x [s]) = prettyTm p s
prettyTm p (IAlternative fc x ss) = "_"
prettyTm p (IRewrite fc s t) = ?dfghkj_13
prettyTm p (IBindHere fc bm s) = ?dfghkj_14
prettyTm p (IBindVar fc str) = str
prettyTm p (IAs fc nameFC side nm s) = ?dfghkj_16
prettyTm p (IMustUnify fc dr s) = ?dfghkj_17
prettyTm p (IDelayed fc LInf s) = showParens (p > Fun) "Inf \{prettyTm Arg s}"
prettyTm p (IDelayed fc LLazy s) = showParens (p > Fun) "Lazy \{prettyTm Arg s}"
prettyTm p (IDelayed fc LUnknown s) = assert_total $ idris_crash "Unexpected LUnknown"
prettyTm p (IDelay fc s) = showParens (p > Fun) "Delay \{prettyTm Arg s}"
prettyTm p (IForce fc s) = showParens (p > Fun) "Force \{prettyTm Arg s}"
prettyTm p (IQuote fc s) = ?dfghkj_21
prettyTm p (IQuoteName fc nm) = ?dfghkj_22
prettyTm p (IQuoteDecl fc decls) = ?dfghkj_23
prettyTm p (IUnquote fc s) = ?dfghkj_24
prettyTm p (IPrimVal fc c) = show c
prettyTm p (IType fc) = "Type"
prettyTm p (IHole fc str) = "?\{str}"
prettyTm p (Implicit fc bindIfUnsolved) = "_"
prettyTm p (IWithUnambigNames fc xs s) = ?dfghkj_29

prettyClause op (PatClause fc lhs rhs) = "\{prettyTm Open lhs} \{op} \{prettyTm Open rhs}"
prettyClause op (WithClause fc lhs rig wval prf flags cls) = ?with_clause
prettyClause op (ImpossibleClause fc lhs) = "\{prettyTm Open lhs} impossible"

prettyDecl local ind (IClaim x) =
    let MkIClaimData count vis opts (MkTy _ n ty) = x.value
        decl = showCount count $ prettyOpts opts $ "\{ind}\{showName n.value} : \{prettyTm Open ty}"
        fc = if not local && isEmptyFC x.fc then "" else "\{ind}-- \{show x.fc}\n"
    in "\{fc}\{show vis} \{decl}"
prettyDecl local ind (IData fc x mtreq dt) = ?rhs_1
prettyDecl local ind (IDef fc nm cls) = concat $ map (\c => prettyClause "=" c ++ "\n") cls
prettyDecl local ind (IParameters fc params decls) = ?rhs_3
prettyDecl local ind (IRecord fc mstr x mtreq rec) = ?rhs_4
prettyDecl local ind (INamespace fc ns decls) =
    let ds = showSep "\n" $ map (prettyDecl local (ind ++ "  ")) decls
    in "\{ind}namespace \{show ns}\n\{ds}"
prettyDecl local ind (ITransform fc nm s t) = ?rhs_6
prettyDecl local ind (IRunElabDecl fc s) = ?rhs_7
prettyDecl local ind (ILog x) = ?rhs_8
prettyDecl local ind (IBuiltin fc bty nm) = ?rhs_9

prettyDecls : List Decl -> String
prettyDecls ds = showSep "\n" $ map (prettyDecl False "") ds

public export
record Import where
    constructor MkImport
    reexport : Bool
    path : ModuleIdent
    nameAs : Maybe Namespace

prettyImport : Import -> String
prettyImport i =
    let kw = if i.reexport then "import public" else "import"
        as = case i.nameAs of
            Just ns => " as \{show ns}"
            Nothing => ""
    in "\{kw} \{show i.path}\{as}\n"

export
prettyModule :
    (mod : ModuleIdent) ->
    (imports : List Import) ->
    (decls : List Decl) ->
    String
prettyModule mod imports decls = unlines
    [ "module \{show mod}"
    , concat $ map prettyImport imports
    , prettyDecls decls
    ]
