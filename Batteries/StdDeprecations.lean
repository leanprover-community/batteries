/-
Copyright (c) 2024 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import Batteries.Tactic.Alias
import Batteries.Data.HashMap
import Batteries.Data.DList
import Batteries.Data.PairingHeap
import Batteries.Data.RBMap
import Batteries.Data.BinomialHeap
import Batteries.Data.UnionFind

/-!
# We set up deprecations for identifiers formerly in the `Std` namespace.

Note that we have not moved anything in the `Std.CodeAction` or `Std.Linter` namespace.

These deprecations do not cover `Std.Tactic`, the contents of which has been moved,
but it would be much harder to generate the deprecations.
Let's hope that people using the tactic implementations can work this out themselves.
-/

@[deprecated] alias Std.AssocList := Batteries.AssocList
@[deprecated] alias Std.HashMap := Batteries.HashMap
@[deprecated] alias Std.mkHashMap := Batteries.mkHashMap
@[deprecated] alias Std.DList := Batteries.DList
@[deprecated] alias Std.PairingHeapImp.Heap := Batteries.PairingHeapImp.Heap
@[deprecated] alias Std.TotalBLE := Batteries.TotalBLE
@[deprecated] alias Std.OrientedCmp := Batteries.OrientedCmp
@[deprecated] alias Std.TransCmp := Batteries.TransCmp
@[deprecated] alias Std.BEqCmp := Batteries.BEqCmp
@[deprecated] alias Std.LTCmp := Batteries.LTCmp
@[deprecated] alias Std.LECmp := Batteries.LECmp
@[deprecated] alias Std.LawfulCmp := Batteries.LawfulCmp
@[deprecated] alias Std.OrientedOrd := Batteries.OrientedOrd
@[deprecated] alias Std.TransOrd := Batteries.TransOrd
@[deprecated] alias Std.BEqOrd := Batteries.BEqOrd
@[deprecated] alias Std.LTOrd := Batteries.LTOrd
@[deprecated] alias Std.LEOrd := Batteries.LEOrd
@[deprecated] alias Std.LawfulOrd := Batteries.LawfulOrd
@[deprecated] alias Std.compareOfLessAndEq_eq_lt := Batteries.compareOfLessAndEq_eq_lt
@[deprecated] alias Std.RBColor := Batteries.RBColor
@[deprecated] alias Std.RBNode := Batteries.RBNode
@[deprecated] alias Std.RBSet := Batteries.RBSet
@[deprecated] alias Std.mkRBSet := Batteries.mkRBSet
@[deprecated] alias Std.RBMap := Batteries.RBMap
@[deprecated] alias Std.mkRBMap := Batteries.mkRBMap
@[deprecated] alias Std.BinomialHeap := Batteries.BinomialHeap
@[deprecated] alias Std.mkBinomialHeap := Batteries.mkBinomialHeap
@[deprecated] alias Std.UFNode := Batteries.UFNode
@[deprecated] alias Std.UnionFind := Batteries.UnionFind

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
