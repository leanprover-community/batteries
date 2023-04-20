import Std.Tactic.Ext
import Std.Logic

set_option linter.missingDocs false
axiom mySorry {α : Sort _} : α

structure A (n : Nat) where
  a : Nat

example (a b : A n) : a = b ∨ True := by
  fail_if_success
    apply Or.inl; ext
  exact Or.inr trivial

structure B (n) extends A n where
  b : Nat
  h : b > 0
  i : Fin b

@[ext] structure C (n) extends B n where
  c : Nat

example (a b : C n) : a = b := by
  ext
  guard_target = a.a = b.a; exact mySorry
  guard_target = a.b = b.b; exact mySorry
  guard_target = HEq a.i b.i; exact mySorry
  guard_target = a.c = b.c; exact mySorry

@[ext (flat := false)] structure C' (n) extends B n where
  c : Nat

example (a b : C' n) : a = b := by
  ext
  guard_target = a.toB = b.toB; exact mySorry
  guard_target = a.c = b.c; exact mySorry

open Std.Tactic.Ext
example (f g : Nat × Nat → Nat) : f = g := by
  ext ⟨x, y⟩
  guard_target = f (x, y) = g (x, y); exact mySorry

-- allow more specific ext theorems
declare_ext_theorems_for Fin
@[ext high] theorem Fin.zero_ext (a b : Fin 0) : True → a = b := by cases a.isLt
example (a b : Fin 0) : a = b := by ext; exact True.intro

def Set (α : Type u) := α → Prop
@[ext] structure LocalEquiv (α : Type u) (β : Type v) where
  source : Set α
@[ext] structure Pretrivialization {F : Type u} (proj : Z → β) extends LocalEquiv Z (β × F) where
  baseSet : Set β
  source_eq : source = baseSet ∘ proj

-- Test for `ext?`: It should apply the two ext lemmas and display that
namespace nested

structure A where
  a : Nat
structure B extends A where
  b : Nat
structure C extends B where
  c : Nat

@[ext]
theorem extCtoB (c₁ c₂ : C) (h : c₁.c = c₂.c) (h' :  c₁.toB = c₂.toB ) : c₁ = c₂ := by admit
@[ext]
theorem extBtoA (b₁ b₂ : B) (h : b₁.b = b₂.b) (h' :  b₁.a = b₂.a ) : b₁ = b₂ := by admit

@[ext]
theorem test (c₁ c₂ : C) (h : c₁.a = c₂.a) (h' :  c₁.b = c₂.b )
    (h'' :  c₁.c = c₂.c ) : c₁ = c₂ := by
  ext?
  repeat assumption
  done

end nested
