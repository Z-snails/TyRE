module TyRE.RE

import Data.DPair
import Data.Either
import Data.Maybe

import TyRE.Core

||| An untyped regular expression indexed by the
||| number of holes it contains
public export
data HoleRE : Nat -> Type where
    HExactly : Char -> HoleRE 0
    HMatch : CharCond -> HoleRE 0
    Hole : HoleRE 1
    HConcat : {l : Nat} -> HoleRE l -> HoleRE r -> HoleRE (l + r)
    HAlt : {l : Nat} -> HoleRE l -> HoleRE r -> HoleRE (l + r)
    HMaybe : HoleRE n -> HoleRE n
    HGroup : HoleRE n -> HoleRE n
    HRep0 : HoleRE n -> HoleRE n
    HRep1 : HoleRE n -> HoleRE n
    HKeep : HoleRE n -> HoleRE n

public export
SomeHoleRE : Type
SomeHoleRE = (h ** HoleRE h)

public export
lift : ({n : Nat} -> HoleRE n -> HoleRE n) -> SomeHoleRE -> SomeHoleRE
lift f (_ ** x) = (_ ** f x)

public export
lift2 :
    ({n, m : Nat} -> HoleRE n -> HoleRE m -> HoleRE (n + m)) ->
    SomeHoleRE -> SomeHoleRE -> SomeHoleRE
lift2 f (_ ** x) (_ ** y) = (_ ** f x y)

||| An untyped regular expression that embeds typed regular
||| expressions
public export
data EmbRE : Type where
    EExactly : Char -> EmbRE
    EMatch : CharCond -> EmbRE
    Emb : {0 ty : Type} -> TyRE ty -> EmbRE
    EConcat : EmbRE -> EmbRE -> EmbRE
    EAlt : EmbRE -> EmbRE -> EmbRE
    EMaybe : EmbRE -> EmbRE
    EGroup : EmbRE -> EmbRE
    ERep0 : EmbRE -> EmbRE
    ERep1 : EmbRE -> EmbRE
    EKeep : EmbRE -> EmbRE

public export
data ExistsVect : Nat -> (f : ix -> Type) -> Type where
    Nil : ExistsVect 0 f
    (::) : {0 ix : _} -> f ix -> ExistsVect k f -> ExistsVect (S k) f

public export
splitAt : (n : Nat) -> ExistsVect (n + m) f -> (ExistsVect n f, ExistsVect m f)
splitAt Z xs = ([], xs)
splitAt (S n) (x :: xs) =
    let (ys, zs) = splitAt n xs
    in (x :: ys, zs)

public export
unhole : HoleRE n -> ExistsVect n TyRE -> EmbRE
unhole (HExactly c) xs = EExactly c
unhole (HMatch c) xs = EMatch c
unhole Hole [x] = Emb x
unhole (HConcat {l} x y) xs =
    let (xs, ys) = splitAt l xs
    in EConcat (unhole x xs) (unhole y ys)
unhole (HAlt {l} x y) xs =
    let (xs, ys) = splitAt l xs
    in EAlt (unhole x xs) (unhole y ys)
unhole (HMaybe x) xs = EMaybe (unhole x xs)
unhole (HGroup x) xs = EGroup (unhole x xs)
unhole (HRep0 x) xs = ERep0 (unhole x xs)
unhole (HRep1 x) xs = ERep1 (unhole x xs)
unhole (HKeep x) xs = EKeep (unhole x xs)

public export
unholeNone : HoleRE n -> {auto 0 noHoles : n = 0} -> EmbRE
unholeNone x = unhole x (rewrite noHoles in [])

public export
data CodeInner : Type where
    EmbC : (0 _ : Type) -> CodeInner
    PairC : CodeInner -> CodeInner -> CodeInner
    EitherC : CodeInner -> CodeInner -> CodeInner
    MaybeC : CodeInner -> CodeInner
    ListC : CodeInner -> CodeInner
    List1C : CodeInner -> CodeInner
    CharC : CodeInner
    StringC : CodeInner
    NatC : CodeInner
    BoolC : CodeInner

data Code = IgnoreC | UnitC | I CodeInner

public export
pairC : Code -> Code -> Code
pairC IgnoreC y = y
pairC UnitC y = y
pairC (I x) IgnoreC = I x
pairC (I x) UnitC = I x
pairC (I x) (I y) = I (PairC x y)

public export
eitherC : Code -> Code -> Code
eitherC IgnoreC IgnoreC = IgnoreC
eitherC IgnoreC UnitC = I BoolC
eitherC IgnoreC (I x) = I $ MaybeC x
eitherC UnitC IgnoreC = I BoolC
eitherC UnitC UnitC = I BoolC
eitherC UnitC (I x) = I $ MaybeC x
eitherC (I x) IgnoreC = I $ MaybeC x
eitherC (I x) UnitC = I $ MaybeC x
eitherC (I x) (I y) = I $ EitherC x y

public export
listC : (CodeInner -> CodeInner) -> Code -> Code
listC list IgnoreC = IgnoreC
listC list UnitC = I NatC
listC list (I x) = I $ list x

public export
maybeC : Code -> Code
maybeC IgnoreC = IgnoreC
maybeC UnitC = I BoolC
maybeC (I x) = I $ MaybeC x

public export
KeepShapeC : EmbRE -> Code
KeepShapeC (EExactly _) = UnitC
KeepShapeC (EMatch x) = I CharC
KeepShapeC (Emb {ty} x) = I $ EmbC ty
KeepShapeC (EConcat x y) = pairC (KeepShapeC x) (KeepShapeC y)
KeepShapeC (EAlt x y) = eitherC (KeepShapeC x) (KeepShapeC y)
KeepShapeC (EMaybe x) = maybeC $ KeepShapeC x
KeepShapeC (EGroup x) = I StringC
KeepShapeC (ERep0 x) = listC ListC $ KeepShapeC x
KeepShapeC (ERep1 x) = listC List1C $ KeepShapeC x
KeepShapeC (EKeep x) = KeepShapeC x

public export
ShapeC : EmbRE -> Code
ShapeC (EExactly _) = IgnoreC
ShapeC (EMatch x) = IgnoreC
ShapeC (Emb {ty} x) = I $ EmbC ty
ShapeC (EConcat x y) = pairC (ShapeC x) (ShapeC y)
ShapeC (EAlt x y) = eitherC (ShapeC x) (ShapeC y)
ShapeC (EMaybe x) = maybeC $ ShapeC x
ShapeC (EGroup x) = I StringC
ShapeC (ERep0 x) = listC ListC $ ShapeC x
ShapeC (ERep1 x) = listC List1C $ ShapeC x
ShapeC (EKeep x) = KeepShapeC x

public export 0
DecodeInner : CodeInner -> Type
DecodeInner (EmbC ty) = ty
DecodeInner (PairC x y) = (DecodeInner x, DecodeInner y)
DecodeInner (EitherC x y) = Either (DecodeInner x) (DecodeInner y)
DecodeInner (MaybeC x) = Maybe (DecodeInner x)
DecodeInner (ListC x) = List (DecodeInner x)
DecodeInner (List1C x) = List1 (DecodeInner x)
DecodeInner CharC = Char
DecodeInner StringC = String
DecodeInner NatC = Nat
DecodeInner BoolC = Bool

public export 0
Decode : Code -> Type
Decode IgnoreC = ()
Decode UnitC = ()
Decode (I c) = DecodeInner c

public export 0
KeepShape, Shape : EmbRE -> Type
Shape = Decode . ShapeC
KeepShape = Decode . KeepShapeC

public export
compileKeep : (e : EmbRE) -> TyRE (KeepShape e)

public export
compileKeep' : (e : EmbRE) -> {auto 0 prf : KeepShapeC e = I code} -> TyRE (DecodeInner code)
compileKeep' e = replace {p = \c => TyRE (Decode c)} prf $ compileKeep e

compileKeep (EExactly c) = match c
compileKeep (EMatch x) = MatchChar x
compileKeep (Emb x) = x

compileKeep (EConcat x y) with (KeepShapeC x) proof px | (KeepShapeC y) proof py
  compileKeep (EConcat x y) | IgnoreC | ys = rewrite sym py in compileKeep x *> compileKeep y
  compileKeep (EConcat x y) | UnitC | ys = rewrite sym py in compileKeep x *> compileKeep y
  compileKeep (EConcat x y) | (I _) | IgnoreC = compileKeep' x <* compileKeep y
  compileKeep (EConcat x y) | (I _) | UnitC = compileKeep' x <* compileKeep y
  compileKeep (EConcat x y) | (I _) | (I _) = compileKeep' x <*> compileKeep' y

compileKeep (EAlt x y) with (KeepShapeC x) proof px | (KeepShapeC y) proof py
  compileKeep (EAlt x y) | IgnoreC | IgnoreC = ignore $ compileKeep x <|> compileKeep y
  compileKeep (EAlt x y) | IgnoreC | UnitC = isRight <$> (compileKeep x <|> compileKeep y)
  compileKeep (EAlt x y) | IgnoreC | (I _) = getRight <$> (compileKeep x <|> compileKeep' y)
  compileKeep (EAlt x y) | UnitC | IgnoreC = isLeft <$> (compileKeep x <|> compileKeep y)
  compileKeep (EAlt x y) | UnitC | UnitC = isLeft <$> (compileKeep x <|> compileKeep y)
  compileKeep (EAlt x y) | UnitC | (I _) = getRight <$> (compileKeep x <|> compileKeep' y)
  compileKeep (EAlt x y) | (I _) | IgnoreC = getLeft <$> (compileKeep' x <|> compileKeep y)
  compileKeep (EAlt x y) | (I _) | UnitC = getLeft <$> (compileKeep' x <|> compileKeep y)
  compileKeep (EAlt x y) | (I _) | (I _) = compileKeep' x <|> compileKeep' y

compileKeep (EMaybe x) with (KeepShapeC x) proof px
  compileKeep (EMaybe x) | IgnoreC = ignore $ option $ compileKeep x
  compileKeep (EMaybe x) | UnitC = isJust <$> option (compileKeep x)
  compileKeep (EMaybe x) | (I _) = option (compileKeep' x)

compileKeep (EGroup x) = group $ compileKeep x

compileKeep (ERep0 x) with (KeepShapeC x) proof px
  compileKeep (ERep0 x) | IgnoreC = ignore $ rep0 $ compileKeep x
  compileKeep (ERep0 x) | UnitC = count0 $ compileKeep x
  compileKeep (ERep0 x) | (I _) = rep0 $ compileKeep' x

compileKeep (ERep1 x) with (KeepShapeC x) proof px
  compileKeep (ERep1 x) | IgnoreC = ignore $ rep1 $ compileKeep x
  compileKeep (ERep1 x) | UnitC = count1 $ compileKeep x
  compileKeep (ERep1 x) | (I _) = rep1l1 $ compileKeep' x

compileKeep (EKeep x) = compileKeep x

public export
compile : (e : EmbRE) -> TyRE (Shape e)

public export
compile' : (e : EmbRE) -> {auto 0 prf : ShapeC e = I code} -> TyRE (DecodeInner code)
compile' e = replace {p = \c => TyRE (Decode c)} prf $ compile e

compile (EExactly c) = match c
compile (EMatch x) = const () <$> MatchChar x
compile (Emb x) = x

compile (EConcat x y) with (ShapeC x) proof px | (ShapeC y) proof py
  compile (EConcat x y) | IgnoreC | ys = rewrite sym py in compile x *> compile y
  compile (EConcat x y) | UnitC | ys = rewrite sym py in compile x *> compile y
  compile (EConcat x y) | (I _) | IgnoreC = compile' x <* compile y
  compile (EConcat x y) | (I _) | UnitC = compile' x <* compile y
  compile (EConcat x y) | (I _) | (I _) = compile' x <*> compile' y

compile (EAlt x y) with (ShapeC x) proof px | (ShapeC y) proof py
  compile (EAlt x y) | IgnoreC | IgnoreC = ignore $ compile x <|> compile y
  compile (EAlt x y) | IgnoreC | UnitC = isRight <$> (compile x <|> compile y)
  compile (EAlt x y) | IgnoreC | (I _) = getRight <$> (compile x <|> compile' y)
  compile (EAlt x y) | UnitC | IgnoreC = isLeft <$> (compile x <|> compile y)
  compile (EAlt x y) | UnitC | UnitC = isLeft <$> (compile x <|> compile y)
  compile (EAlt x y) | UnitC | (I _) = getRight <$> (compile x <|> compile' y)
  compile (EAlt x y) | (I _) | IgnoreC = getLeft <$> (compile' x <|> compile y)
  compile (EAlt x y) | (I _) | UnitC = getLeft <$> (compile' x <|> compile y)
  compile (EAlt x y) | (I _) | (I _) = compile' x <|> compile' y

compile (EMaybe x) with (ShapeC x) proof px
  compile (EMaybe x) | IgnoreC = ignore $ option $ compile x
  compile (EMaybe x) | UnitC = isJust <$> option (compile x)
  compile (EMaybe x) | (I _) = option (compile' x)

compile (EGroup x) = group $ compile x

compile (ERep0 x) with (ShapeC x) proof px
  compile (ERep0 x) | IgnoreC = ignore $ rep0 $ compile x
  compile (ERep0 x) | UnitC = count0 $ compile x
  compile (ERep0 x) | (I _) = rep0 $ compile' x

compile (ERep1 x) with (ShapeC x) proof px
  compile (ERep1 x) | IgnoreC = ignore $ rep1 $ compile x
  compile (ERep1 x) | UnitC = count1 $ compile x
  compile (ERep1 x) | (I _) = rep1l1 $ compile' x

compile (EKeep x) = compileKeep x
