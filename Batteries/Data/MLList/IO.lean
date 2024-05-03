/-
Copyright (c) 2023 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Batteries.Lean.System.IO
import Batteries.Data.MLList.Basic

/-!
# IO operations using monadic lazy lists.
-/

namespace MLList

/--
Give a list of tasks, return the monadic lazy list which
returns the values as they become available.
-/
def ofTaskList (tasks : List (Task α)) : MLList BaseIO α :=
  fix?' (init := tasks) fun t => do
    if h : 0 < t.length then
      some <$> IO.waitAny' t h
    else
      pure none
