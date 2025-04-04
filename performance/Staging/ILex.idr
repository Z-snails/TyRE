module Staging.ILex

import Data.Bool
import Text.ILex
import Text.ILex.Val
import Language.Reflection

%language ElabReflection

ToType () where
    toType_ = TO $ Plain "Unit"

ignore : Expr b e is (os :< a) -> Expr b e is (os :< ())
ignore e = mmap (const ()) e

%macro
marr2 : (f : a -> b -> c) -> Elab (Expr False e (is :< a :< b) (is :< c))
marr2 f = lift {a = a -> b -> c} f <&> \v => arr2 v

repA : Expr False LexErr is (is :< SnocList ())
repA = many (ignore $ chr 'a') >>> eoi

times : Expr False LexErr is (is :< SnocList (Nat, Nat))
times = many time >>> eoi
  where
    add : Val (Char -> Char -> Nat)
    add = mlift (\x, y => 10 * cast (toDigit x) + cast (toDigit y))

    hour : forall is. Expr True LexErr is (is :< Nat)
    hour = (range '0' '1' >>> range '0' '9' >>> arr2 add)
        <|> (chr '2' >>> range '0' '3' >>> arr2 add)

    minute : forall is. Expr True LexErr is (is :< Nat)
    minute = range '0' '5' >>> range '0' '9' >>> arr2 add

    pairNatNat : Val (Nat -> Nat -> (Nat, Nat))
    pairNatNat = mlift (\x, y => (x, y))

    time : forall is. Expr True LexErr is (is :< (Nat, Nat))
    time = hour >>> chr_ ':' >>> minute >>> arr2 pairNatNat

main : IO ()
main = do
    putStrLn
      """
        module Staging.ILexGenerated
        import public Text.ILex.Util
        %default total
        """
    putStrLn $ generate "lexRepA" repA
    putStrLn $ generate "lexTimes" times

