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
keepArg (Named n@(UN _) x) = not $ isOp n
keepArg (Named _ _) = False
keepArg _ = True

prettyOpts : List FnOpt -> String -> Either String String
prettyOpts [] s = pure s
prettyOpts (o :: os) s = do
    o <- case o of
        Inline => pure "%inline "
        NoInline => pure "%noinline "
        Deprecate => pure "%deprecate "
        TCInline => pure "%tcinline "
        (Hint normal) => pure $ if normal then "%hint " else "%chaser "
        (GlobalHint normal) => pure $ if normal then "%globalhint " else "%defaulthint "
        ExternFn => pure "%extern"
        (ForeignFn ss) => Left "foreign"
        (ForeignExport ss) => Left "foreign export"
        Invertible => Left "invertible"
        (Totality treq) => pure $ show treq ++ " "
        Macro => pure $ "%macro "
        (SpecArgs nms) => Left "%spec"
    (o ++) <$> prettyOpts os s

prettyTm : Pos -> TTImp -> Either String String
prettyClause : String -> Clause -> Either String String
prettyDecl : (local : Bool) -> (indent : String) -> Decl -> Either String String

prettyApp : Pos -> TTImp -> Either String String
prettyApp p t = do
    let (f, xs) = asApp t []
    let xs = filter keepArg xs
    f' <- prettyTm Fun f
    xs' <- traverse prettyArgument xs
    pure $ showParens (p > Fun) $ showSep " " (f' :: xs')
  where
    prettyArgument : Argument -> Either String String
    prettyArgument (Positional s) = prettyTm Arg s
    prettyArgument (Named nm s) = pure "{\{showName nm} = \{!(prettyTm Open s)}}"
    prettyArgument (Auto s) = pure "@{\{!(prettyTm Open s)}}"
    prettyArgument (With s) = Left "with application"

isPair : TTImp -> Maybe (TTImp, TTImp)
isPair (IApp _ (IApp _ (IVar _ `{Pair}) x) y) = Just (x, y)
isPair _ = Nothing

isMkPair : TTImp -> Maybe (TTImp, TTImp)
isMkPair (IApp _ (IApp _ (IVar _ `{MkPair}) x) y) = Just (x, y)
isMkPair _ = Nothing

tryPair : TTImp -> TTImp -> Maybe (Either String String)
tryPair x y = do
    (x, y) <- isPair x <* isMkPair y
        <|> isMkPair x <* isPair y
    Just $ (\x, y => "(\{x}, \{y})") <$> prettyTm Open x <*> prettyTm Open y

isUnit : TTImp -> Bool
isUnit (IVar _ `{Unit}) = True
isUnit _ = False

isMkUnit : TTImp -> Bool
isMkUnit (IVar _ `{MkUnit}) = True
isMkUnit _ = False

tryUnit : TTImp -> TTImp -> Maybe (Either String String)
tryUnit x y = if (isUnit x && isMkUnit y) || (isMkUnit x && isUnit y)
    then Just (Right "()")
    else Nothing

prettyAlternative : List TTImp -> Either String String
prettyAlternative [x, y] = case the _ (tryPair x y <|> tryUnit x y) of
    Nothing => Left "alternative (overloading)"
    Just (Left e) => Left e
    Just (Right x) => Right x
prettyAlternative _ = Left "alternative"

prettyTm p (IVar fc nm) = pure $ showName nm
prettyTm p (IPi fc rig pinfo mnm argTy retTy) = do
    let n = maybe "_" showName mnm
    argTy <- prettyTm Open argTy
    retTy <- prettyTm Open retTy
    showParens (p > Fun) <$> case pinfo of
        ImplicitArg => pure "{\{showCount rig n} : \{argTy}} -> \{retTy}"
        ExplicitArg => pure "(\{showCount rig n} : \{argTy}) -> \{retTy}"
        AutoImplicit => pure "{auto \{showCount rig n} : \{argTy}} -> \{retTy}"
        (DefImplicit x) => do
            x <- prettyTm Arg x
            pure $ "{default \{x} \{showCount rig n} : \{argTy}} -> \{retTy}"
prettyTm p (ILam fc rig pinfo mnm argTy scope) = do
    let n = maybe "_" showName mnm
    scope <- prettyTm Open scope
    pure $ showParens (p > Open) "\\ \{n} => \{scope}"
prettyTm p (ILet fc lhsFC rig nm nTy nVal scope) = do
    nTy <- prettyTm Open nTy
    nVal <- prettyTm Open nVal
    scope <- prettyTm Open scope
    pure $ showParens (p > Open)
        "let \{showCount rig $ showName nm} : \{nTy} := \{nVal} in \{scope}"
prettyTm p (ICase fc xs s ty cls) = do
    cls <- showSep " ; " <$> traverse (prettyClause "=>") cls
    scr <- prettyTm Open s
    pure $ showParens (p > Open) "case \{scr} of { \{cls} }"
prettyTm p (ILocal fc decls s) = do
    bind <- showSep "; " <$> traverse (prettyDecl True "") decls
    pure $ "let \{bind} in \{!(prettyTm Open s)}"
prettyTm p (IUpdate fc upds s) = Left "record update"
prettyTm p t@(IApp _ _ _) = prettyApp p t
prettyTm p t@(INamedApp _ _ _ _) = prettyApp p t
prettyTm p t@(IAutoApp _ _ _) = prettyApp p t
prettyTm p t@(IWithApp _ _ _) = prettyApp p t
prettyTm p (ISearch fc depth) = pure "%search"
prettyTm p (IAlternative fc x [s]) = prettyTm p s
prettyTm p (IAlternative fc x ss) = prettyAlternative ss
prettyTm p (IRewrite fc s t) = pure $ showParens (p > Open) $ "rewrite \{!(prettyTm Open s)} in \{!(prettyTm Open t)}"
prettyTm p (IBindHere fc bm s) = Left "IBindHere"
prettyTm p (IBindVar fc str) = pure str
prettyTm p (IAs fc nameFC side nm s) = Left "@ patterns"
prettyTm p (IMustUnify fc dr s) = Left "dotted patterns"
prettyTm p (IDelayed fc LInf s) = pure $ showParens (p > Fun) "Inf \{!(prettyTm Arg s)}"
prettyTm p (IDelayed fc LLazy s) = pure $ showParens (p > Fun) "Lazy \{!(prettyTm Arg s)}"
prettyTm p (IDelayed fc LUnknown s) = assert_total $ idris_crash "Unexpected LUnknown"
prettyTm p (IDelay fc s) = pure $ showParens (p > Fun) "Delay \{!(prettyTm Arg s)}"
prettyTm p (IForce fc s) = pure $ showParens (p > Fun) "Force \{!(prettyTm Arg s)}"
prettyTm p (IQuote fc s) = Left "quotes"
prettyTm p (IQuoteName fc nm) = Left "quotes"
prettyTm p (IQuoteDecl fc decls) = Left "quotes"
prettyTm p (IUnquote fc s) = Left "unquotes"
prettyTm p (IPrimVal fc c) = pure $ show c
prettyTm p (IType fc) = pure "Type"
prettyTm p (IHole fc str) = pure "?\{str}"
prettyTm p (Implicit fc True) = pure "_"
prettyTm p (Implicit fc False) = pure "?"
prettyTm p (IWithUnambigNames fc xs s) = Left "with disambiguation"

prettyClause op (PatClause fc lhs rhs) = pure "\{!(prettyTm Open lhs)} \{op} \{!(prettyTm Open rhs)}"
prettyClause op (WithClause fc lhs rig wval prf flags cls) = Left "with clause"
prettyClause op (ImpossibleClause fc lhs) = pure "\{!(prettyTm Open lhs)} impossible"

prettyDecl local ind (IClaim x) = do
    let MkIClaimData count vis opts (MkTy _ n ty) = x.value
    ty <- prettyTm Open ty
    let decl = showCount count $ !(prettyOpts opts "\{ind}\{showName n.value} : \{ty}")
    let fc = if not local && isEmptyFC x.fc then "" else "\{ind}-- \{show x.fc}\n"
    pure "\{fc}\{show vis} \{decl}"
prettyDecl local ind (IData fc x mtreq dt) = Left "data"
prettyDecl local ind (IDef fc nm cls) = concat <$> traverse (\c => (++ "\n") <$> prettyClause "=" c) cls
prettyDecl local ind (IParameters fc params decls) = Left "parameters"
prettyDecl local ind (IRecord fc mstr x mtreq rec) = Left "record"
prettyDecl local ind (INamespace fc ns decls) = do
    ds <- showSep "\n" <$> traverse (prettyDecl local (ind ++ "  ")) decls
    pure "\{ind}namespace \{show ns}\n\{ds}"
prettyDecl local ind (ITransform fc nm s t) = Left "%transform"
prettyDecl local ind (IRunElabDecl fc s) = Left "%runElab"
prettyDecl local ind (ILog x) = Left "%logging"
prettyDecl local ind (IBuiltin fc bty nm) = Left "%builtin"

export
prettyDecls : List Decl -> Either String String
prettyDecls ds = showSep "\n" <$> traverse (prettyDecl False "") ds

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
    Either String String
prettyModule mod imports decls = pure $ unlines
    [ "module \{show mod}"
    , concat $ map prettyImport imports
    , !(prettyDecls decls)
    ]
