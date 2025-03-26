module TyRE.Extra.Elab

import Language.Reflection

isModPart : String -> Bool
isModPart x = case unpack x of
    [] => False
    c :: cs => isUpper c && all isAlpha cs

unAsModPart : UserName -> Maybe String
unAsModPart (Basic n) = if isModPart n then Just n else Nothing
unAsModPart _ = Nothing

nsAsModParts : Namespace -> List String
nsAsModParts (MkNS ns) = ns

export
nameAsMod : Name -> Maybe ModuleIdent
nameAsMod (UN n) = Just (MkMI [!(unAsModPart n)])
nameAsMod (NS ns (UN n)) = Just (MkMI (!(unAsModPart n) :: nsAsModParts ns))
nameAsMod _ = Nothing

Show ModuleIdent where
    show (MkMI mi) = showSep "." (reverse mi)

Show OriginDesc where
    show (PhysicalIdrSrc id) = show id
    show (PhysicalPkgSrc fname) = fname
    show (Virtual Interactive) = "repl"

fcComment : FC -> String
fcComment EmptyFC = ""
fcComment (MkFC origin start _) = "-- \{show origin}:\{show start}"
fcComment (MkVirtualFC origin start _) = "-- \{show origin}:\{show start}"

Show FnOpt where
    show Inline = ?dfgkh_0
    show NoInline = ?dfgkh_1
    show Deprecate = ?dfgkh_2
    show TCInline = ?dfgkh_3
    show (Hint x) = ?dfgkh_4
    show (GlobalHint x) = ?dfgkh_5
    show ExternFn = ?dfgkh_6
    show (ForeignFn ss) = ?dfgkh_7
    show (ForeignExport ss) = ?dfgkh_8
    show Invertible = ?dfgkh_9
    show (Totality treq) = ?dfgkh_10
    show Macro = ?dfgkh_11
    show (SpecArgs nms) = ?dfgkh_12

showOpts : List FnOpt -> String
showOpts os = concat $ map (\o => show o ++ " ") os

data IdrTm : Type
data IdrClause : Type

data IdrTm : Type where
    Var : Name -> IdrTm
    Case : IdrTm -> List IdrClause -> IdrTm
    App : IdrTm -> List IdrTm -> IdrTm

underscore : IdrTm
underscore = Var $ UN Underscore

record IdrClause where
    constructor MkClause
    lhs : IdrTm
    rhs : IdrTm

Show IdrClause where
    show c = "\{assert_total $ showPrec Open c} => \{assert_total $ showPrec Open c}"

Show IdrTm where
    showPrec p (Var nm) = showPrefix True nm
    showPrec p (Case x cls) =
        let cls = showSep "," $ assert_total $ map show cls
        in "case \{showPrec Open x} of { \{cls} }"
    showPrec p (App x xs) = ?fdghk_2
