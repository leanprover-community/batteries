/-
Copyright (c) 2023 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Batteries.Lean.System.IO
public import Batteries.Data.MLList.Basic

deprecated_module "It is recommended to use `Std.IterM` instead." (since := "2026-07-06")

@[expose] public section

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
