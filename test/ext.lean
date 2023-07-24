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

-- Check that we generate a warning if there are too many patterns.
example (f g : Nat → Nat) (h : f = g) : f = g := by
  ext i j
  exact h ▸ rfl

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

structure MyUnit

@[ext high] theorem MyUnit.ext1 (x y : MyUnit) (_h : 0 = 1) : x = y := rfl
@[ext high] theorem MyUnit.ext2 (x y : MyUnit) (_h : 1 = 1) : x = y := rfl
@[ext] theorem MyUnit.ext3 (x y : MyUnit) (_h : 2 = 1) : x = y := rfl

example (x y : MyUnit) : x = y := by ext; rfl

-- Check that we don't generate a warning when `x` only uses a pattern in one branch:
attribute [ext] Prod
example (f : ℕ × (ℕ → ℕ)) : f = f := by
  ext x
  · rfl
  · guard_target = (f.2) x = (f.2) x
    rfl

example (f : Empty → Empty) : f = f := by
  ext ⟨⟩

@[ext] theorem ext_intros {n m : Nat} (w : ∀ n m : Nat, n = m) : n = m := by apply w

example : 3 = 7 := by
  ext : 1
  rename_i n m
  guard_target = n = m
  admit

example : 3 = 7 := by
  ext n m : 1
  guard_target = n = m
  admit

/-!
## Test for `ext?`
It should apply the two ext lemmas and display a tactic replacement
-/
namespace nested

structure A where
  a : Nat
structure B extends A where
  b : Nat
structure C extends B where
  c : Nat

@[ext]
theorem extCtoB (c₁ c₂ : C) (g : ∀ (a : A), true)  (h : c₁.c = c₂.c) (h' :  c₁.toB = c₂.toB ) :
    c₁ = c₂ := by admit
@[ext]
theorem extBtoA (b₁ b₂ : B) (h : b₁.b = b₂.b) (h' :  b₁.a = b₂.a ) : b₁ = b₂ := by admit

@[ext]
theorem test (c₁ c₂ : C) (h : c₁.a = c₂.a) (h' :  c₁.b = c₂.b )
    (h'' :  c₁.c = c₂.c ) : c₁ = c₂ := by
  ext?
  -- Try this:
  -- · apply extCtoB
  --   intros
  --   sorry
  --   sorry
  --   apply extBtoA
  --   sorry
  --   sorry
  repeat admit

/-!
## Testing `ext!?`

`ext` does not find the lemma `extCtoB` above because it does not see through the
definition `D := C`. `ext!?` ignores the types and tries to apply anything brute force
giving a warning if it succeeds.
-/

def D := C

@[ext]
theorem test₂ (c₁ c₂ : D) (h : c₁.a = c₂.a) (h' :  c₁.b = c₂.b )
    (h'' :  c₁.c = c₂.c ) : c₁ = c₂ := by
  ext!?
  -- `nested.extCtoB` applied, which is written in terms of type `nested.C`.
  -- If you want `ext` to find it, please make a copy of this
  -- lemma in terms of type `D`.
  repeat admit

end nested
