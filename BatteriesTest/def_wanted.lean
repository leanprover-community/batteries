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
info: @vec_of_some : {d_some_nat : some_nat.Val} → DerivedWanted (Vector Nat d_some_nat)
-/
#guard_msgs in #check @vec_of_some

/-! Repeated references to the same bracket share one parameter binder. -/
def_wanted vec_double :
    Vector Nat (❰some_nat❱ + ❰some_nat❱) := Vector.replicate _ 0

/--
info: @vec_double : {d_some_nat : some_nat.Val} → DerivedWanted (Vector Nat (d_some_nat + d_some_nat))
-/
#guard_msgs in #check @vec_double

/-! Multiple distinct brackets each get their own parameter, in order of first occurrence. -/
def_wanted vec_two_lengths :
    Vector Nat (❰some_nat❱ + ❰other_nat❱) := Vector.replicate _ 0

/--
info: @vec_two_lengths : {d_some_nat : some_nat.Val} →
  {d_other_nat : other_nat.Val} → DerivedWanted (Vector Nat (d_some_nat + d_other_nat))
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
info: @one_fin : {h_zero_eq_one : zero_eq_one.Stmt} → DerivedWanted (Fin 50)
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

/-! ## Bodies

A `def_wanted` *with* a body is **transparent**: it is emitted as a genuine `@[reducible]` definition
(wrapped in `DerivedWanted` so it cannot be used directly as a value of its type), and `❰foo❱`
*inlines* it. So `foo`'s own `❰…❱` references do not become `d_foo` binders on the referrer; only the
opaque *leaf* holes survive. A bodyless `def_wanted` stays an opaque `DefWanted` hole. -/

def_wanted any_nat_plus_one : Nat := ❰any_nat❱ + 1

/--
info: @any_nat_plus_one : {d_any_nat : any_nat.Val} → DerivedWanted Nat
-/
#guard_msgs in #check @any_nat_plus_one

/-! A body that doesn't type-check is rejected. -/
/--
error: Application type mismatch: The argument
  d_any_nat✝
has type
  any_nat.Val
but is expected to have type
  Bool
in the application
  { val := d_any_nat✝ }
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
info: @use_param_dw : {d_param_dw : (n : Nat) → (param_dw n).Val} → DerivedWanted (Fin 4)
-/
#guard_msgs in #check @use_param_dw

/-! Multiple binders, mixing implicit and explicit. -/

def_wanted param_many {α : Type} (xs : List α) (n : Nat) : Option α
def_wanted use_param_many : Option Nat := ❰param_many❱ [1, 2, 3] 0

/--
info: @use_param_many : {d_param_many : {α : Type} → (xs : List α) → (n : Nat) → (param_many xs n).Val} →
  DerivedWanted (Option Nat)
-/
#guard_msgs in #check @use_param_many

/-! Universe-polymorphic references work when the use site shares the universe variable. -/

universe u
def_wanted poly_dw (α : Type u) : Type u
def_wanted use_poly_dw (α : Type u) : Type u := ❰poly_dw❱ α

/--
info: use_poly_dw : Type u_1 → {d_poly_dw : (α : Type u_1) → (poly_dw α).Val} → DerivedWanted (Type u_1)
-/
#guard_msgs in #check @use_poly_dw

/-! A universe-polymorphic `def_wanted` may equally be referenced at a *concrete* universe: the
generated binder spells `poly_dw`'s universe as a hole, so `❰poly_dw❱ Nat` resolves at `Type` rather
than pinning the reference to a rigid universe parameter that no concrete type could match. -/
def_wanted use_poly_concrete : Type := ❰poly_dw❱ Nat

/--
info: @use_poly_concrete : {d_poly_dw : (α : Type) → (poly_dw α).Val} → DerivedWanted Type
-/
#guard_msgs in #check @use_poly_concrete

/-! ## Transitive dependencies

A transparent (body-ful) wanted is inlined at each reference, so referencing it surfaces only the
opaque *leaf* holes it ultimately depends on — never the transparent intermediates. Class-valued and
proof leaves are surfaced too. -/

def_wanted base_dep (R : Type) : Nat
def_wanted derived_dep (R : Type) : Nat := ❰base_dep❱ R + 1

/-- `derived_dep` is transparent, so referencing it inlines its body; only its leaf hole `base_dep`
surfaces as a `d_base_dep` binder (there is no `d_derived_dep`). -/
def_wanted use_chain : Nat := ❰derived_dep❱ Nat

/--
info: @use_chain : {d_base_dep : (R : Type) → (base_dep R).Val} → DerivedWanted Nat
-/
#guard_msgs in #check @use_chain

/-! A transparent `def_wanted` (`foo_dep`) referencing a `theorem_wanted` (`boo_dep`) inlines,
leaving only the proof leaf hole `h_boo_dep` (Filippo Nuccio's reported shape). The inlined `foo_dep`
shows as an η-expanded projection in the recorded statement. -/

theorem_wanted boo_dep (R : Type) : (0 : Nat) < 5
def_wanted foo_dep (R : Type) : Fin 5 := ⟨0, ❰boo_dep❱ R⟩
theorem_wanted ref_with_proof_dep : (❰foo_dep❱ Nat).val = 0

/--
info: @ref_with_proof_dep : {h_boo_dep : ∀ (R : Type), (boo_dep R).Stmt} → ProofWanted (↑((fun R => (foo_dep R).val) Nat) = 0)
-/
#guard_msgs in #check @ref_with_proof_dep

/-- Deduplication still applies: `base_dep` referenced both directly and (transitively, via the
inlined `derived_dep`) yields a single `d_base_dep` binder. -/
def_wanted use_chain_and_base : Nat := ❰base_dep❱ Nat + ❰derived_dep❱ Nat

/--
info: @use_chain_and_base : {d_base_dep : (R : Type) → (base_dep R).Val} → DerivedWanted Nat
-/
#guard_msgs in #check @use_chain_and_base

/-! A chain of transparent defs inlines all the way down: referencing the top surfaces only the
single opaque leaf hole. -/

def_wanted leaf_dep (R : Type) : Nat
def_wanted mid_dep (R : Type) : Nat := ❰leaf_dep❱ R + 1
def_wanted top_dep (R : Type) : Nat := ❰mid_dep❱ R + 1
def_wanted use_three_levels : Nat := ❰top_dep❱ Nat

/--
info: @use_three_levels : {d_leaf_dep : (R : Type) → (leaf_dep R).Val} → DerivedWanted Nat
-/
#guard_msgs in #check @use_three_levels

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

A wanted typeclass instance is registered like `instance`, so Lean's typeclass synth can find it in
later wanted declarations with no explicit `❰…❱`. This is *include-on-use* (like `variable [inst]`):
a later declaration carries the instance binder only when its statement or body actually needs it. -/

namespace InstWantedTests
private class MyClass (α : Type) where val : α
private def use_val {α} [MyClass α] : α := MyClass.val

instance_wanted myInst : MyClass Nat

/-! A declaration that *uses* the instance picks it up automatically: `use_val` needs `[MyClass Nat]`,
discharged by `myInst`, so the binder appears. -/
def_wanted usesInstance : (use_val : Nat) = use_val

/--
info: @usesInstance : [d_myInst : myInst.Val] → DefWanted (use_val = use_val)
-/
#guard_msgs in #check @usesInstance

/-! A declaration that does *not* use it does not carry it (include-on-use): `Nat` needs no
`MyClass`, so no binder appears. -/
def_wanted needsNoInstance : Nat

/--
info: needsNoInstance : DefWanted Nat
-/
#guard_msgs in #check @needsNoInstance

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

/-! Anonymous instances get a non-hygienic, user-resolvable name from the class head. `MyClass Bool`
does not need the earlier `myInst : MyClass Nat`, so (by include-on-use) it carries no binder. -/
instance_wanted : MyClass Bool

/--
info: instMyClass : DefWanted (MyClass Bool)
-/
#guard_msgs in #check @instMyClass

/-! A second anonymous instance of the same class head gets a `_1` suffix to avoid colliding
with the first. Neither uses the earlier instances, so neither carries their binders. -/
private class OtherClass (α : Type) where val : α
instance_wanted : OtherClass Nat
instance_wanted : OtherClass Bool

/--
info: instOtherClass : DefWanted (OtherClass Nat)
-/
#guard_msgs in #check @instOtherClass

/--
info: instOtherClass_1 : DefWanted (OtherClass Bool)
-/
#guard_msgs in #check @instOtherClass_1

/-! A non-class payload is rejected. -/
/--
error: `instance_wanted` requires a typeclass payload; use `def_wanted` for non-class data
-/
#guard_msgs in instance_wanted bad : 5 = 7

end InstWantedTests
