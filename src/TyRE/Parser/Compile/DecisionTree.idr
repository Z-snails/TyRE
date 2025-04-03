module TyRE.Parser.Compile.DecisionTree

import Data.SortedSet
import Data.List
import Data.Fin
import Data.Nat

%default total

%hide Prelude.Range

public export
data Op a = Lt a | Lte a | Eq a | Gte a | OFalse | OTrue

public export
data DecTree : Type -> Type where
    Pure : Op a -> DecTree a
    If : Op a -> DecTree a -> DecTree a -> DecTree a

data Range : Type -> Type where
    MkRange : a -> a -> Range a

next : Char -> Char
next c =
    let c' = chr (ord c + 1)
    in if c' == chr 0 then c else c'

compact : List (Range Char) -> List (Range Char)
compact [] = []
compact (MkRange c1 c2 :: es) = case compact es of
    [] => [MkRange c1 c2]
    (MkRange c3 c4 :: es) => if next c2 >= c3
        then MkRange c1 c4 :: es
        else MkRange c1 c2 :: MkRange c3 c4 :: es

data BinTree : Type -> Type where
    Empty : BinTree a
    Leaf : a -> BinTree a
    Node : BinTree a -> a -> BinTree a -> BinTree a

splitNat : Nat -> (Nat, Nat)
splitNat k =
    let k = natToInteger k
        k2 = k `div` 2
    in if k `mod` 2 == 0
        then (cast k2, cast $ k2 - 1)
        else (cast k2, cast k2)

splitMaybe : List a -> Nat -> Maybe (List a, a, List a)
splitMaybe [] _ = Nothing
splitMaybe (x :: xs) Z = Just ([], x, xs)
splitMaybe (x :: xs) (S k) = do
    (ls, m, rs) <- splitMaybe xs k
    Just (x :: ls, m, rs)

asBinTree : List a -> BinTree a
asBinTree xs = go xs (length xs)
  where
    go : List a -> Nat -> BinTree a
    go xs 0 = Empty
    go xs k =
        let (l, r) = splitNat k
            Just (ls, m, rs) = splitMaybe xs l
                | Nothing => Empty
        in Node (go ls (assert_smaller k l)) m (go rs (assert_smaller k r))

export
rangeTreeToDecTree : Eq a => BinTree (Range a) -> DecTree a
rangeTreeToDecTree Empty = Pure OFalse
rangeTreeToDecTree (Leaf (MkRange x y)) = if x == y then Pure (Eq x) else If (Gte x) (Pure (Lte y)) (Pure OFalse)
rangeTreeToDecTree (Node l (MkRange x y) r) =
    let l = rangeTreeToDecTree l
        r = rangeTreeToDecTree r
    in If (Lt x) l (If (Lte y) (Pure OTrue) r)

export
makeDecTree : Eq a => SortedSet a -> DecTree a
makeDecTree s = rangeTreeToDecTree $ asBinTree $ map (\x => MkRange x x) $ Prelude.toList s
