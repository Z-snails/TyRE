module Test

import System.Clock
import TyRE.Parser.Compile
import TyRE.Parser

import Data.List
import Data.Regex
import Language.Reflection

import Data.Fin
import Data.SortedSet
import Data.DPair
import Data.SnocList
import Syntax.PreorderReasoning

import TyRE.Core
import TyRE.Parser.GroupThompson
import public TyRE.Parser.Compile.Runtime

import Data.Regex

%language ElabReflection

simple : CompiledSM Unit
simple = %runElab doCompile Empty
