module TyRE.Parser.GroupThompson

import Data.List
import Data.List1
import Data.SortedSet
import Data.Maybe

import TyRE.Core

%default total

public export
State : Type
State = Integer

public export
record NextStates where
  constructor MkNextStates
  condition : CharCond
  isSat : List (Maybe State)

public export
record GroupSM where
  constructor MkGroupSM
  initStates : List (Maybe State)
  statesWithNext : List (State, NextStates)
  max : State

public export
replaceEndInInit : List (Maybe a) -> List (Maybe a) -> List (Maybe a)
replaceEndInInit xs mks =
  case find isNothing xs of
    Nothing => xs
    Just _ => mks ++ (filter isJust xs)

public export
replaceEndInNext : List (State, NextStates) -> List (Maybe State)
                -> List (State, NextStates)
replaceEndInNext [] mks = []
replaceEndInNext ((n, (MkNextStates condition isSat)) :: xs) mks =
  (n, (MkNextStates condition (replaceEndInInit isSat mks))) :: (replaceEndInNext xs mks)

public export
groupStates : State -> TyRE a -> GroupSM
groupStates n (MatchChar cond) =
  MkGroupSM [Just n] [(n, MkNextStates cond [Nothing])] (n+1)
groupStates n (Group re) = groupStates n re
groupStates n Empty =  MkGroupSM [Nothing] [] n
groupStates n (re1 <*> re2) =
  let (MkGroupSM init1 sWN1 n1) := groupStates n re1
      (MkGroupSM init2 sWN2 n2) := groupStates n1 re2
  in MkGroupSM  (replaceEndInInit init1 init2)
                ((replaceEndInNext sWN1 init2)  ++ sWN2)
                n2
groupStates n (re1 <|> re2) =
  let (MkGroupSM init1 sWN1 n1) := groupStates n re1
      (MkGroupSM init2 sWN2 n2) := groupStates n1 re2
  in MkGroupSM (init1 ++ init2) (sWN1 ++ sWN2) n2
groupStates n (Rep re) =
  let (MkGroupSM init sWN n') := groupStates n re
  in MkGroupSM (Nothing :: init) (replaceEndInNext sWN (Nothing :: init)) n'
groupStates n (Conv re f) = groupStates n re

public export
eq : List (Maybe State) -> List (Maybe State) -> Bool
eq mks mjs = (Data.SortedSet.fromList mks) == (fromList mjs)

public export
min : GroupSM -> GroupSM
min (MkGroupSM initStates statesWithNext max) =
  let (initStates', statesWithNext') := go (length statesWithNext) (initStates, statesWithNext)
  in MkGroupSM initStates' statesWithNext' max where
  go : Nat -> (List (Maybe State), List (State, NextStates)) -> (List (Maybe State), List (State, NextStates))
  go 0 xs = xs
  go (S k) (init, xs) =
    let mappings := getMappings (group xs)
    in if (length mappings == 0) then (init, xs) else go k (squash mappings (init, xs)) where
    group : List (State, NextStates) -> List (List1 (State, NextStates))
    group xs = groupBy stateEq xs where
      stateEq : (State, NextStates) -> (State, NextStates) -> Bool
      stateEq (_, (MkNextStates cond  isSat ))
              (_, (MkNextStates cond' isSat')) =
                cond == cond' && (eq isSat isSat')
    getMappings : List (List1 (State, NextStates)) -> List (State, State)
    getMappings [] = []
    getMappings (((nh, _) ::: xs) :: ys) = (map (\case (x, _) => (nh, x)) xs) ++ getMappings ys
    applyFilter : (State, State) -> List (Maybe State) -> List (Maybe State)
    applyFilter (n, n1) xs =
      case (find (== Just n1) xs) of
        Nothing => xs
        (Just y) => (Just n) :: filter (\x => not (x == Just n || x == Just n1)) xs
    squash : List (State, State) -> (List (Maybe State), List (State, NextStates)) -> (List (Maybe State), List (State, NextStates))
    squash [] x = x
    squash ((n, n1) :: xs) (init, ys) =
      squash xs
            ( filter (\x => x /= (Just n1)) init
            , applyMap ys) where
            applyMap : List (State, NextStates) -> List (State, NextStates)
            applyMap [] = []
            applyMap ((n', y) :: xs) =
              if (n' == n1) then applyMap xs
              else  ( n'
                    , MkNextStates  y.condition
                                    (applyFilter (n, n1) y.isSat)) :: applyMap xs

public export
groupSM : TyRE a -> GroupSM
groupSM re = min (groupStates 0 re)
-- groupSM re = groupStates 0 re
