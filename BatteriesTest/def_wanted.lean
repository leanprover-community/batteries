import Batteries.Util.ProofWanted

/-!
# Tests for `def_wanted`

Parallel to `BatteriesTest/theorem_wanted.lean`; covers the same shapes plus the cross-references
between `proof_wanted` and `def_wanted` that the shared bracket allows.
-/

/-! No unused variable warnings, even though `x` is only mentioned in the statement. -/
#guard_msgs in def_wanted no_unused_warning_dw (x : Nat) : Fin (x + 1)

/-! After elaboration, the wanted type lives in the env as a `DefWanted`. -/
def_wanted prime_dec : ∀ n : Nat, Decidable (n = n)

/--
info: prime_dec : DefWanted ((n : Nat) → Decidable (n = n))
-/
#guard_msgs in #check @prime_dec

/-! ## Bracket references

When the recorded result type mentions a parameter (here via the length of a `Vector`), it
pretty-prints with its `d_…` name; otherwise it shows anonymously. -/

def_wanted some_nat : Nat
def_wanted other_nat : Nat

def_wanted vec_of_some : Vector Nat (❰some_nat❱) := Vector.replicate _ 0

/--
info: @vec_of_some : {d_some_nat : some_nat.Val} → DefWanted (Vector Nat d_some_nat)
-/
#guard_msgs in #check @vec_of_some

/-! Repeated references to the same bracket share one parameter binder. -/
def_wanted vec_double :
    Vector Nat (❰some_nat❱ + ❰some_nat❱) := Vector.replicate _ 0

/--
info: @vec_double : {d_some_nat : some_nat.Val} → DefWanted (Vector Nat (d_some_nat + d_some_nat))
-/
#guard_msgs in #check @vec_double

/-! Multiple distinct brackets each get their own parameter, in order of first occurrence. -/
def_wanted vec_two_lengths :
    Vector Nat (❰some_nat❱ + ❰other_nat❱) := Vector.replicate _ 0

/--
info: @vec_two_lengths : {d_some_nat : some_nat.Val} →
  {d_other_nat : other_nat.Val} → DefWanted (Vector Nat (d_some_nat + d_other_nat))
-/
#guard_msgs in #check @vec_two_lengths

/-! ## Cross-references

A reference's parameter prefix (`h_` for `theorem_wanted`, `d_` for `def_wanted`) follows
the *referenced* declaration's kind. -/

theorem_wanted zero_eq_one : (0 : Nat) = 1
def_wanted any_nat : Nat

theorem_wanted any_nat_eq_self : ❰any_nat❱ = ❰any_nat❱ := rfl

/--
info: @any_nat_eq_self : {d_any_nat : any_nat.Val} → ProofWanted (d_any_nat = d_any_nat)
-/
#guard_msgs in #check @any_nat_eq_self

def_wanted one_fin : Fin 50 := ⟨0, by rw [show (0 : Nat) = 1 from ❰zero_eq_one❱]; decide⟩

/--
info: @one_fin : {h_zero_eq_one : zero_eq_one.Stmt} → DefWanted (Fin 50)
-/
#guard_msgs in #check @one_fin

/-! ## Error cases -/

/-! Referencing an unknown identifier. -/
/--
error: Unknown constant `not_declared`
-/
#guard_msgs in def_wanted bad_unknown_dw : ❰not_declared❱

/-! Referencing a regular `def` (neither a `ProofWanted` nor a `DefWanted`). -/
private def regular_def_dw : Nat := 0

/--
error: `regular_def_dw` is not a `theorem_wanted`, `proof_wanted`, or `def_wanted` declaration (its type doesn't end in `ProofWanted _` or `DefWanted _`)
-/
#guard_msgs in def_wanted bad_not_wanted : ❰regular_def_dw❱

/-! `❰…❱` in a binder type is rejected explicitly. -/
/--
error: `❰…❱` may not appear inside binder type of `def_wanted`
-/
#guard_msgs in def_wanted bad_in_binder_dw (h : ❰prime_dec❱) : True

/-! Unlike `proof_wanted`, `def_wanted` accepts non-`Prop` statements (that's the point)
and also allows `Prop` statements (any `Sort` is fine). -/
#guard_msgs in def_wanted is_prop : True
#guard_msgs in def_wanted is_type : Nat

/-! ## Bodies -/

def_wanted any_nat_plus_one : Nat := ❰any_nat❱ + 1

/--
info: @any_nat_plus_one : {d_any_nat : any_nat.Val} → DefWanted Nat
-/
#guard_msgs in #check @any_nat_plus_one

/-! A body that doesn't type-check is rejected. -/
/--
error: Type mismatch
  d_any_nat✝
has type
  any_nat.Val
but is expected to have type
  Bool
-/
#guard_msgs in def_wanted bad_body_dw : Bool := ❰any_nat❱

/-! A body with no `❰…❱` reference anywhere falls back to a `def` suggestion. -/
/--
info: Try this:
  [apply] def trivially_unit : Unit :=
    ()
---
error: `def_wanted` with a body but no `❰…❱` reference is just a `def`; either replace `def_wanted` with `def`, or reference another `theorem_wanted` / `proof_wanted` / `def_wanted` / `instance_wanted` via `❰…❱` in the statement or body
-/
#guard_msgs in def_wanted trivially_unit : Unit := ()

/-! ## Parametrised references

(The corresponding cases for parametrised `proof_wanted` refs are in
`BatteriesTest/theorem_wanted.lean`.) -/

def_wanted param_dw (n : Nat) : Fin (n + 1)

def_wanted use_param_dw : Fin 4 := ❰param_dw❱ 3

/--
info: @use_param_dw : {d_param_dw : (n : Nat) → (param_dw n).Val} → DefWanted (Fin 4)
-/
#guard_msgs in #check @use_param_dw

/-! Multiple binders, mixing implicit and explicit. -/

def_wanted param_many {α : Type} (xs : List α) (n : Nat) : Option α
def_wanted use_param_many : Option Nat := ❰param_many❱ [1, 2, 3] 0

/--
info: @use_param_many : {d_param_many : {α : Type} → (xs : List α) → (n : Nat) → (param_many xs n).Val} →
  DefWanted (Option Nat)
-/
#guard_msgs in #check @use_param_many

/-! Universe-polymorphic references work when the use site shares the universe variable. -/

universe u
def_wanted poly_dw (α : Type u) : Type u
def_wanted use_poly_dw (α : Type u) : Type u := ❰poly_dw❱ α

/--
info: use_poly_dw : Type u_1 → {d_poly_dw : (α : Type u_1) → (poly_dw α).Val} → DefWanted (Type u_1)
-/
#guard_msgs in #check @use_poly_dw

/-! A universe-polymorphic `def_wanted` may equally be referenced at a *concrete* universe: the generated
binder spells `poly_dw`'s universe as a hole, so `❰poly_dw❱ Nat` resolves at `Type` rather than
pinning the reference to a rigid universe parameter that no concrete type could match. -/
def_wanted use_poly_concrete : Type := ❰poly_dw❱ Nat

/--
info: @use_poly_concrete : {d_poly_dw : (α : Type) → (poly_dw α).Val} → DefWanted Type
-/
#guard_msgs in #check @use_poly_concrete

/-! ## Namespacing -/

namespace M
  def_wanted ns_foo : Nat

  /-- Bracket resolution works on namespaced names; the generated parameter uses just the last
      component of the name. -/
  def_wanted ns_bar : Nat := ❰ns_foo❱ + 1
end M

/-! ## Soundness

A `def_wanted` must *not* be usable as an inhabitant of its declared type. The
placeholder has type `DefWanted T`, not `T`, so any attempt to use it as a value should
fail to typecheck. -/

/--
error: Type mismatch
  any_nat
has type
  DefWanted Nat
but is expected to have type
  Nat
-/
#guard_msgs in example : Nat := any_nat

/-! ## `instance_wanted`

A wanted typeclass instance: registered like `instance` so Lean's typeclass synth picks it up
automatically in every subsequent wanted declaration, with no explicit `❰…❱` reference. -/

namespace InstWantedTests
private class MyClass (α : Type) where val : α
private def use_val {α} [MyClass α] : α := MyClass.val

instance_wanted myInst : MyClass Nat

/-! Subsequent wanted decls auto-include `myInst` as an instance binder, so typeclass synth
finds it (`needsInstance` has no body so the rule "a body must reference a `❰…❱`" doesn't
apply; the auto-include alone makes the signature carry `[myInst.Val]`). -/
def_wanted needsInstance : Nat

/--
info: @needsInstance : [myInst.Val] → DefWanted Nat
-/
#guard_msgs in #check @needsInstance

/-! The "body needs a `❰…❱`" rule looks only at *user-written* refs: an ambient
`instance_wanted` registration does not stand in for an explicit bracket. -/
/--
info: Try this:
  [apply] def body_with_only_auto_include : Nat :=
    use_val
---
error: `def_wanted` with a body but no `❰…❱` reference is just a `def`; either replace `def_wanted` with `def`, or reference another `theorem_wanted` / `proof_wanted` / `def_wanted` / `instance_wanted` via `❰…❱` in the statement or body
-/
#guard_msgs in def_wanted body_with_only_auto_include : Nat := use_val

/-! Anonymous instances get a non-hygienic, user-resolvable name from the class head. (The
signature also picks up `[myInst.Val]` because `myInst` is itself an `instance_wanted`
declared earlier.) -/
instance_wanted : MyClass Bool

/--
info: @instMyClass : [myInst.Val] → DefWanted (MyClass Bool)
-/
#guard_msgs in #check @instMyClass

/-! A second anonymous instance of the same class head gets a `_1` suffix to avoid colliding
with the first. -/
private class OtherClass (α : Type) where val : α
instance_wanted : OtherClass Nat
instance_wanted : OtherClass Bool

/--
info: @instOtherClass : [myInst.Val] → [[d_myInst : myInst.Val] → instMyClass.Val] → DefWanted (OtherClass Nat)
-/
#guard_msgs in #check @instOtherClass

/--
info: @instOtherClass_1 : [myInst.Val] →
  [[d_myInst : myInst.Val] → instMyClass.Val] →
    [[d_myInst : myInst.Val] → [d_instMyClass : [d_myInst : myInst.Val] → instMyClass.Val] → instOtherClass.Val] →
      DefWanted (OtherClass Bool)
-/
#guard_msgs in #check @instOtherClass_1

/-! A non-class payload is rejected. -/
/--
error: `instance_wanted` requires a typeclass payload; use `def_wanted` for non-class data
-/
#guard_msgs in instance_wanted bad : 5 = 7

end InstWantedTests
