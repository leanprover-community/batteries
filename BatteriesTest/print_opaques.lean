import Batteries.Tactic.PrintOpaques

partial def foo : Unit → Nat := foo
def bar : Unit → Nat := foo

/--
info: 'bar' depends on opaque or partial definitions: [foo]
-/
#guard_msgs in
#print opaques bar

opaque qux : Nat
def quux : Bool := qux == 0

/--
info: 'quux' depends on opaque or partial definitions: [qux]
-/
#guard_msgs in
#print opaques quux

/-! Examples from the documentation. -/

/--
info: 'Classical.choice' depends on opaque or partial definitions: [Classical.choice]
-/
#guard_msgs in
#print opaques Classical.choice

/--
info: 'Classical.axiomOfChoice' does not use any opaque or partial definitions
-/
#guard_msgs in
#print opaques Classical.axiomOfChoice

/--
info: 'Std.HashMap.insert' depends on opaque or partial definitions: [System.Platform.getNumBits,
UInt64.toUSize]
-/
#guard_msgs in
#print opaques Std.HashMap.insert

/--
info: 'Stream.forIn' depends on opaque or partial definitions: [Stream.forIn.visit]
-/
#guard_msgs in
#print opaques Stream.forIn
