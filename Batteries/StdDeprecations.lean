/-
Copyright (c) 2024 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import Batteries.Tactic.Alias
import Batteries.Data.DList
import Batteries.Data.PairingHeap
import Batteries.Data.BinomialHeap.Basic
import Batteries.Data.HashMap.Basic
import Batteries.Data.RBMap.Basic
import Batteries.Data.UnionFind.Basic

/-!
# We set up deprecations for identifiers formerly in the `Std` namespace.

Note that we have not moved anything in the `Std.CodeAction` or `Std.Linter` namespace.

These deprecations do not cover `Std.Tactic`, the contents of which has been moved,
but it would be much harder to generate the deprecations.
Let's hope that people using the tactic implementations can work this out themselves.
-/

@[deprecated (since := "2024-05-07")] alias Std.AssocList := Batteries.AssocList
@[deprecated (since := "2024-05-07")] alias Std.mkHashMap := Batteries.mkHashMap
@[deprecated (since := "2024-05-07")] alias Std.DList := Batteries.DList
@[deprecated (since := "2024-05-07")] alias Std.PairingHeapImp.Heap := Batteries.PairingHeapImp.Heap
@[deprecated (since := "2024-05-07")] alias Std.TotalBLE := Batteries.TotalBLE
@[deprecated (since := "2024-05-07")] alias Std.OrientedCmp := Batteries.OrientedCmp
@[deprecated (since := "2024-05-07")] alias Std.TransCmp := Batteries.TransCmp
@[deprecated (since := "2024-05-07")] alias Std.BEqCmp := Batteries.BEqCmp
@[deprecated (since := "2024-05-07")] alias Std.LTCmp := Batteries.LTCmp
@[deprecated (since := "2024-05-07")] alias Std.LECmp := Batteries.LECmp
@[deprecated (since := "2024-05-07")] alias Std.LawfulCmp := Batteries.LawfulCmp
@[deprecated (since := "2024-05-07")] alias Std.OrientedOrd := Batteries.OrientedOrd
@[deprecated (since := "2024-05-07")] alias Std.TransOrd := Batteries.TransOrd
@[deprecated (since := "2024-05-07")] alias Std.BEqOrd := Batteries.BEqOrd
@[deprecated (since := "2024-05-07")] alias Std.LTOrd := Batteries.LTOrd
@[deprecated (since := "2024-05-07")] alias Std.LEOrd := Batteries.LEOrd
@[deprecated (since := "2024-05-07")] alias Std.LawfulOrd := Batteries.LawfulOrd
@[deprecated (since := "2024-05-07")]
alias Std.compareOfLessAndEq_eq_lt := Batteries.compareOfLessAndEq_eq_lt
@[deprecated (since := "2024-05-07")] alias Std.RBColor := Batteries.RBColor
@[deprecated (since := "2024-05-07")] alias Std.RBNode := Batteries.RBNode
@[deprecated (since := "2024-05-07")] alias Std.RBSet := Batteries.RBSet
@[deprecated (since := "2024-05-07")] alias Std.mkRBSet := Batteries.mkRBSet
@[deprecated (since := "2024-05-07")] alias Std.RBMap := Batteries.RBMap
@[deprecated (since := "2024-05-07")] alias Std.mkRBMap := Batteries.mkRBMap
@[deprecated (since := "2024-05-07")] alias Std.BinomialHeap := Batteries.BinomialHeap
@[deprecated (since := "2024-05-07")] alias Std.mkBinomialHeap := Batteries.mkBinomialHeap
@[deprecated (since := "2024-05-07")] alias Std.UFNode := Batteries.UFNode
@[deprecated (since := "2024-05-07")] alias Std.UnionFind := Batteries.UnionFind

-- Check that these generate usable deprecated hints
-- when referring to names inside these namespaces.
set_option warningAsError true in
/--
error: `Std.UnionFind` has been deprecated, use `Batteries.UnionFind` instead
---
error: unknown constant 'Std.UnionFind.find'
-/
#guard_msgs in
#eval Std.UnionFind.find
