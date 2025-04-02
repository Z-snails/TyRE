module TyRE.Hole

import Data.DPair
import Data.Either

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
data Code : Type where
    EmbC : (0 _ : Type) -> Code
    UnitC : Code
    PairC : Code -> Code -> Code
    EitherC : Code -> Code -> Code
    MaybeC : Code -> Code
    ListC : Code -> Code
    List1C : Code -> Code
    CharC : Code
    StringC : Code
    NatC : Code

public export
pairC : Maybe Code -> Maybe Code -> Maybe Code
pairC (Just x) (Just y) = Just (PairC x y)
pairC (Just x) Nothing = Just x
pairC Nothing (Just y) = Just y
pairC Nothing Nothing = Nothing

public export
eitherC : Maybe Code -> Maybe Code -> Maybe Code
eitherC Nothing Nothing = Nothing
eitherC (Just x) Nothing = Just $ MaybeC x
eitherC Nothing (Just y) = Just $ MaybeC y
eitherC (Just x) (Just y) = Just $ EitherC x y

public export
listC : Maybe Code -> Code
listC Nothing = NatC
listC (Just c) = ListC c

public export
list1C : Maybe Code -> Code
list1C Nothing = NatC
list1C (Just c) = List1C c

public export
KeepShapeC : EmbRE -> Maybe Code
KeepShapeC (EExactly _) = Just UnitC
KeepShapeC (EMatch x) = Just CharC
KeepShapeC (Emb {ty} x) = Just $ EmbC ty
KeepShapeC (EConcat x y) = pairC (KeepShapeC x) (KeepShapeC y)
KeepShapeC (EAlt x y) = eitherC (KeepShapeC x) (KeepShapeC y)
KeepShapeC (EMaybe x) = MaybeC <$> KeepShapeC x
KeepShapeC (EGroup x) = Just StringC
KeepShapeC (ERep0 x) = Just $ listC $ KeepShapeC x
KeepShapeC (ERep1 x) = Just $ list1C $ KeepShapeC x
KeepShapeC (EKeep x) = KeepShapeC x

public export
ShapeC : EmbRE -> Maybe Code
ShapeC (EExactly _) = Nothing
ShapeC (EMatch x) = Nothing
ShapeC (Emb {ty} x) = Just $ EmbC ty
ShapeC (EConcat x y) = pairC (ShapeC x) (ShapeC y)
ShapeC (EAlt x y) = eitherC (ShapeC x) (ShapeC y)
ShapeC (EMaybe x) = MaybeC <$> ShapeC x
ShapeC (EGroup x) = Just StringC
ShapeC (ERep0 x) = Just $ listC $ ShapeC x
ShapeC (ERep1 x) = Just $ list1C $ ShapeC x
ShapeC (EKeep x) = KeepShapeC x

public export 0
Decode : Code -> Type
Decode (EmbC ty) = ty
Decode UnitC = ()
Decode (PairC x y) = (Decode x, Decode y)
Decode (EitherC x y) = Either (Decode x) (Decode y)
Decode (MaybeC x) = Maybe (Decode x)
Decode (ListC x) = List (Decode x)
Decode (List1C x) = List1 (Decode x)
Decode NatC = Nat
Decode CharC = Char
Decode StringC = String

public export 0
DecodeMaybe : Maybe Code -> Type
DecodeMaybe Nothing = ()
DecodeMaybe (Just c) = Decode c

public export 0
KeepShape, Shape : EmbRE -> Type
Shape = DecodeMaybe . ShapeC
KeepShape = DecodeMaybe . KeepShapeC

public export
compileKeep : (e : EmbRE) -> TyRE (KeepShape e)

public export
compileKeep' : (e : EmbRE) -> {auto 0 prf : KeepShapeC e = Just code} -> TyRE (Decode code)
compileKeep' e = replace {p = \c => TyRE (DecodeMaybe c)} prf $ compileKeep e

compileKeep (EExactly c) = match c
compileKeep (EMatch x) = MatchChar x
compileKeep (Emb x) = x

compileKeep (EConcat x y) with (KeepShapeC x) proof px | (KeepShapeC y) proof py
  compileKeep (EConcat x y) | Just _ | Just _ = compileKeep' x <*> compileKeep' y
  compileKeep (EConcat x y) | Nothing | Just _ = compileKeep x *> compileKeep' y
  compileKeep (EConcat x y) | Just _ | Nothing = compileKeep' x <* compileKeep y
  compileKeep (EConcat x y) | Nothing | Nothing = ignore $ compileKeep x <*> compileKeep y

compileKeep (EAlt x y) with (KeepShapeC x) proof px | (KeepShapeC y) proof py
  compileKeep (EAlt x y) | Just _ | Just _ = compileKeep' x <|> compileKeep' y
  compileKeep (EAlt x y) | Nothing | Just _ = getRight <$> (compileKeep x <|> compileKeep' y)
  compileKeep (EAlt x y) | Just _ | Nothing = getLeft <$> (compileKeep' x <|> compileKeep y)
  compileKeep (EAlt x y) | Nothing | Nothing = ignore $ (compileKeep x <|> compileKeep y)

compileKeep (EMaybe x) with (KeepShapeC x) proof px
  compileKeep (EMaybe x) | Just _ = option $ compileKeep' x
  compileKeep (EMaybe x) | Nothing = ignore $ option $ compileKeep x

compileKeep (EGroup x) = group $ compileKeep x

compileKeep (ERep0 x) with (KeepShapeC x) proof px
  compileKeep (ERep0 x) | Just _ = rep0 $ compileKeep' x
  compileKeep (ERep0 x) | Nothing = map length $ rep0 $ compileKeep x

compileKeep (ERep1 x) with (KeepShapeC x) proof px
  compileKeep (ERep1 x) | Just _ = rep1l1 $ compileKeep' x
  compileKeep (ERep1 x) | Nothing = map length $ rep1l1 $ compileKeep x

compileKeep (EKeep x) = compileKeep x

public export
compile : (e : EmbRE) -> TyRE (Shape e)

public export
compile' : (e : EmbRE) -> {auto 0 prf : ShapeC e = Just code} -> TyRE (Decode code)
compile' e = replace {p = \c => TyRE (DecodeMaybe c)} prf $ compile e

compile (EExactly c) = match c
compile (EMatch x) = ignore $ MatchChar x
compile (Emb x) = x

compile (EConcat x y) with (ShapeC x) proof px | (ShapeC y) proof py
  compile (EConcat x y) | Just _ | Just _ = compile' x <*> compile' y
  compile (EConcat x y) | Nothing | Just _ = compile x *> compile' y
  compile (EConcat x y) | Just _ | Nothing = compile' x <* compile y
  compile (EConcat x y) | Nothing | Nothing = ignore $ compile x <*> compile y

compile (EAlt x y) with (ShapeC x) proof px | (ShapeC y) proof py
  compile (EAlt x y) | Just _ | Just _ = compile' x <|> compile' y
  compile (EAlt x y) | Nothing | Just _ = getRight <$> (compile x <|> compile' y)
  compile (EAlt x y) | Just _ | Nothing = getLeft <$> (compile' x <|> compile y)
  compile (EAlt x y) | Nothing | Nothing = ignore $ (compile x <|> compile y)

compile (EMaybe x) with (ShapeC x) proof px
  compile (EMaybe x) | Just _ = option $ compile' x
  compile (EMaybe x) | Nothing = ignore $ option $ compile x

compile (EGroup x) = group $ compile x

compile (ERep0 x) with (ShapeC x) proof px
  compile (ERep0 x) | Just _ = rep0 $ compile' x
  compile (ERep0 x) | Nothing = map length $ rep0 $ compile x

compile (ERep1 x) with (ShapeC x) proof px
  compile (ERep1 x) | Just _ = rep1l1 $ compile' x
  compile (ERep1 x) | Nothing = map length $ rep1l1 $ compile x

compile (EKeep x) = compileKeep x
