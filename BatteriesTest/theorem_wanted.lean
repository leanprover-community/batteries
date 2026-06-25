import Batteries.Util.ProofWanted

/-!
# Tests for `theorem_wanted`

`proof_wanted` is an accepted synonym for `theorem_wanted`; the `## Synonym` section below checks
that it behaves identically.
-/

/-! No unused variable warnings, even though `x` is only mentioned in the statement. -/
#guard_msgs in theorem_wanted no_unused_warning (x : Nat) : x = x

/-! After elaboration, the wanted statement lives in the env as a `ProofWanted`. -/
theorem_wanted env_trace : 17 = 37

/--
info: env_trace : ProofWanted (17 = 37)
-/
#guard_msgs in #check @env_trace

/-! ## Bracket references -/

/-! Forward reference via `❰…❱` works: the resulting statement records "if env_trace then …". -/
theorem_wanted with_ref :
    (⟨17, by rw [❰env_trace❱]; decide⟩ : Fin 50) = 0

/-! Repeated references to the same bracket share one hypothesis binder. -/
theorem_wanted double_ref :
    (⟨17, by rw [❰env_trace❱]; decide⟩ : Fin 50)
      = (⟨17, by rw [❰env_trace❱]; decide⟩ : Fin 50)

/--
info: @double_ref : {h_env_trace : env_trace.Stmt} → ProofWanted (⟨17, ⋯⟩ = ⟨17, ⋯⟩)
-/
#guard_msgs in #check @double_ref

/-! Multiple distinct brackets each get their own hypothesis. -/
theorem_wanted other_eq : 5 = 11

theorem_wanted two_refs :
    (⟨17, by rw [❰env_trace❱]; decide⟩ : Fin 50)
      = (⟨5, by rw [❰other_eq❱]; decide⟩ : Fin 50)

/-! Two distinct brackets produce two distinct binders, in order of first occurrence. -/
/--
info: @two_refs : {h_env_trace : env_trace.Stmt} → {h_other_eq : other_eq.Stmt} → ProofWanted (⟨17, ⋯⟩ = ⟨5, ⋯⟩)
-/
#guard_msgs in #check @two_refs

/-! ## Parametrised references

`❰foo❱` applied to arguments works when `foo` has its own binders. -/

theorem_wanted param_tw (n : Nat) : n = n

theorem_wanted ref_param_tw :
    (⟨5, by rw [❰param_tw❱ 5]; decide⟩ : Fin 50) = 0

/--
info: @ref_param_tw : {h_param_tw : ∀ (n : Nat), (param_tw n).Stmt} → ProofWanted (⟨5, ⋯⟩ = 0)
-/
#guard_msgs in #check @ref_param_tw

/-! Implicit binders. The printed `param_imp.Stmt` drops the implicit argument cosmetically; the
underlying type retains it (see `set_option pp.all true`). -/

theorem_wanted param_imp {n : Nat} : n = n

theorem_wanted ref_param_imp :
    (⟨5, by rw [show (5 : Nat) = 5 from ❰param_imp❱]; decide⟩ : Fin 50) = 0

/--
info: @ref_param_imp : {h_param_imp : ∀ {n : Nat}, param_imp.Stmt} → ProofWanted (⟨5, ⋯⟩ = 0)
-/
#guard_msgs in #check @ref_param_imp

/-! Instance binders. `❰param_inst❱` resolves the instance from context. -/

theorem_wanted param_inst [Decidable True] : True

theorem_wanted ref_param_inst :
    (⟨0, by have : True := ❰param_inst❱; decide⟩ : Fin 50) = 0

/--
info: @ref_param_inst : {h_param_inst : ∀ [inst : Decidable True], param_inst.Stmt} → ProofWanted (⟨0, ⋯⟩ = 0)
-/
#guard_msgs in #check @ref_param_inst

/-! Multiple dependent binders. -/

theorem_wanted param_many (n : Nat) (h : n > 0) : n - 1 < n

theorem_wanted ref_param_many :
    (⟨3, by have := ❰param_many❱ 4 (by decide); omega⟩ : Fin 50) = ⟨3, by decide⟩

/--
info: @ref_param_many : {h_param_many : ∀ (n : Nat) (h : n > 0), (param_many n h).Stmt} → ProofWanted (⟨3, ⋯⟩ = ⟨3, ⋯⟩)
-/
#guard_msgs in #check @ref_param_many

/-! ## Error cases -/

/-! Referencing an unknown identifier. -/
/--
error: Unknown constant `not_declared`
-/
#guard_msgs in theorem_wanted bad_unknown : ❰not_declared❱

/-! Referencing a regular `def` (not a `ProofWanted`). -/
private def regular_def : Nat := 0

/--
error: `regular_def` is not a `theorem_wanted`, `proof_wanted`, or `def_wanted` declaration (its type doesn't end in `ProofWanted _` or `DefWanted _`)
-/
#guard_msgs in theorem_wanted bad_not_tw : ❰regular_def❱

/-! Referencing a hand-rolled `ProofWanted` whose statement isn't a `Prop`. -/
private def fake_pw : ProofWanted Nat := ⟨⟩

/--
error: `fake_pw` is a `ProofWanted`, but its statement is not a proposition
-/
#guard_msgs in theorem_wanted bad_not_prop : ❰fake_pw❱

/-! Using `❰…❱` outside `theorem_wanted` / `proof_wanted` / `def_wanted` / `instance_wanted`. -/
/--
error: `❰…❱` may only appear inside the statement or body of `theorem_wanted`, `proof_wanted`, `def_wanted`, or `instance_wanted`
-/
#guard_msgs in example : True := ❰env_trace❱

/-! `❰…❱` in a binder type is rejected explicitly. -/
/--
error: `❰…❱` may not appear inside binder type of `theorem_wanted`
-/
#guard_msgs in theorem_wanted bad_in_binder (h : ❰env_trace❱) : True

/-! When the statement isn't a proposition the `: Prop` ascription rejects it. -/
/--
error: Type mismatch
  Nat
has type
  Type
of sort `Type 1` but is expected to have type
  Prop
of sort `Type`
-/
#guard_msgs in theorem_wanted bad_not_a_prop (x : Nat) : Nat

/-! ## Bodies -/

private def foo : Nat := 17
theorem_wanted foo_eq_37 : foo = 37
theorem_wanted thirtyseven_eq_41 : (37 : Nat) = 41

/-! Body-only references still become binders on the recorded placeholder. -/
theorem_wanted foo_eq_41 : foo = 41 := by
  rw [❰foo_eq_37❱]; exact ❰thirtyseven_eq_41❱

/--
info: @foo_eq_41 : {h_foo_eq_37 : foo_eq_37.Stmt} → {h_thirtyseven_eq_41 : thirtyseven_eq_41.Stmt} → ProofWanted (foo = 41)
-/
#guard_msgs in #check @foo_eq_41

/-! A reference shared between statement and body is deduplicated. -/
theorem_wanted foo_eq_41_fin :
    (⟨foo, by rw [❰foo_eq_37❱]; decide⟩ : Fin 50) = ⟨41, by decide⟩ := by
  apply Fin.ext
  show foo = 41
  rw [❰foo_eq_37❱]; exact ❰thirtyseven_eq_41❱

/--
info: @foo_eq_41_fin : {h_foo_eq_37 : foo_eq_37.Stmt} →
  {h_thirtyseven_eq_41 : thirtyseven_eq_41.Stmt} → ProofWanted (⟨foo, ⋯⟩ = ⟨41, ⋯⟩)
-/
#guard_msgs in #check @foo_eq_41_fin

/-! A body that doesn't type-check is rejected; the bracket has already been substituted for the
hypothesis binder by the time the error is reported. -/
/--
error: Type mismatch
  h_foo_eq_37✝
has type
  foo_eq_37.Stmt
but is expected to have type
  foo + 1 = 38
-/
#guard_msgs in theorem_wanted bad_body : foo + 1 = 38 := ❰foo_eq_37❱

/-! A body may reference a parametrised `theorem_wanted`. -/

theorem_wanted foo_param (m : Nat) : foo = m

theorem_wanted foo_eq_99 : foo = 99 := ❰foo_param❱ 99

/--
info: @foo_eq_99 : {h_foo_param : ∀ (m : Nat), (foo_param m).Stmt} → ProofWanted (foo = 99)
-/
#guard_msgs in #check @foo_eq_99

/-! A body with no `❰…❱` reference anywhere is rejected with a `Try this:` pointing at
`theorem`. -/
/--
info: Try this:
  [apply] theorem trivially_true : True :=
    trivial
---
error: `theorem_wanted` with a body but no `❰…❱` reference is just a `theorem`; either replace `theorem_wanted` with `theorem`, or reference another `theorem_wanted` / `proof_wanted` / `def_wanted` / `instance_wanted` via `❰…❱` in the statement or body
-/
#guard_msgs in theorem_wanted trivially_true : True := trivial

/-! ## Universe-polymorphic references

A reference to a universe-polymorphic wanted declaration is usable at a single use-site universe:
the generated hypothesis binder spells the reference's universe levels as holes, so they unify with
whatever universe the reference is used at (here `u`, distinct from the referenced `w`). -/

theorem_wanted exists_ulift.{w} : ∃ x : ULift.{w} Nat, x.down = 1

theorem_wanted exists_ulift_down.{u} : ∃ x : ULift.{u} Nat, x.down = 1 := by
  obtain ⟨x : ULift.{u} Nat, hx⟩ := ❰exists_ulift❱
  exact ⟨x, hx⟩

/--
info: @exists_ulift_down : {h_exists_ulift : exists_ulift.Stmt} → ProofWanted (∃ x, x.down = 1)
-/
#guard_msgs in #check @exists_ulift_down

/-! When the referenced declaration carries a binder whose *type* mentions its universe parameter
(`{α : Type _}`), that universe is also spelled as a hole in the generated hypothesis, so the
reference may be used at a concrete universe — here `Array Nat` at `Type` — not just at a shared
universe variable. -/

theorem_wanted size_poly {α : Type _} (a : Array α) (x y : α) :
    ((a.push x).push y).size = a.size + 2

theorem_wanted ref_size_concrete (a : Array Nat) (x y : Nat) :
    ((a.push x).push y).size = a.size + 2 := ❰size_poly❱ a x y

/--
info: ref_size_concrete : (a : Array Nat) →
  (x y : Nat) →
    {h_size_poly : ∀ {α : Type} (a : Array α) (x y : α), (size_poly a x y).Stmt} →
      ProofWanted (((a.push x).push y).size = a.size + 2)
-/
#guard_msgs in #check @ref_size_concrete

/-! TODO: a single `❰…❱` reference desugars to one hypothesis binder, which is monomorphic in
universes. Using that one reference at two *different* universes therefore fails: the binder unifies
with the first use's universe (`u` below) and the second use (`v`) then mismatches. Lifting this
would need a universe-polymorphic hypothesis, which the term language can't express; the alternative
is a separate wanted declaration per universe. Flagged for future contributors. -/
/--
error: Type mismatch
  h_exists_ulift✝
has type
  ProofWanted.Stmt.{0} exists_ulift.{u}
but is expected to have type
  Exists.{v + 1} fun y => Eq.{1} (ULift.down.{v, 0} y) 1
-/
#guard_msgs in
set_option pp.universes true in
theorem_wanted exists_ulift_two.{u, v} :
    ∃ x : ULift.{u} Nat, ∃ y : ULift.{v} Nat, x.down = y.down := by
  have hu : ∃ x : ULift.{u} Nat, x.down = 1 := ❰exists_ulift❱
  have hv : ∃ y : ULift.{v} Nat, y.down = 1 := ❰exists_ulift❱
  obtain ⟨x, hx⟩ := hu
  obtain ⟨y, hy⟩ := hv
  exact ⟨x, y, hx.trans hy.symm⟩

/-! ## Namespacing -/

namespace N
  theorem_wanted ns_foo : 17 = 37

  /-- Bracket resolution works on namespaced names; the generated hypothesis uses just the last
      component of the name. -/
  theorem_wanted ns_bar :
      (⟨17, by rw [❰ns_foo❱]; decide⟩ : Fin 50) = 0
end N

/-! ## Soundness

A `theorem_wanted` must *not* be usable as a proof of its statement. The placeholder has type
`ProofWanted T`, not `T`, so any attempt to use it as a proof should fail to typecheck. -/

/--
error: Type mismatch
  env_trace
has type
  ProofWanted (17 = 37)
of sort `Type` but is expected to have type
  17 = 37
of sort `Prop`
-/
#guard_msgs in example : 17 = 37 := env_trace

/-- And the bracket itself is not a term-level escape hatch: outside `theorem_wanted` it errors,
and inside `theorem_wanted` it only adds a hypothesis to the recorded statement. So even chained
`theorem_wanted`s never produce a real proof, only a wanted theorem of the form "if … then …". -/
example : True := trivial

/-! ## Synonym

`proof_wanted` is an accepted synonym for `theorem_wanted` (expected to be deprecated eventually).
It shares the elaborator, so it records the same `ProofWanted` placeholder, reports its own keyword
in error messages, and cross-references `theorem_wanted` / `def_wanted` freely. -/

proof_wanted syn_basic : 1 = 1

/--
info: syn_basic : ProofWanted (1 = 1)
-/
#guard_msgs in #check @syn_basic

/-! A `proof_wanted` body with no `❰…❱` reference reports the `proof_wanted` keyword. -/
/--
info: Try this:
  [apply] theorem syn_trivial : True :=
    trivial
---
error: `proof_wanted` with a body but no `❰…❱` reference is just a `theorem`; either replace `proof_wanted` with `theorem`, or reference another `theorem_wanted` / `proof_wanted` / `def_wanted` / `instance_wanted` via `❰…❱` in the statement or body
-/
#guard_msgs in proof_wanted syn_trivial : True := trivial

/-! `proof_wanted` and `theorem_wanted` cross-reference each other; the binder prefix is `h_`
either way, since both record a `ProofWanted`. -/
proof_wanted syn_a : (0 : Nat) = 1

theorem_wanted syn_b : ❰syn_a❱ = ❰syn_a❱ := rfl

/--
info: @syn_b : {h_syn_a : syn_a.Stmt} → ProofWanted (h_syn_a = h_syn_a)
-/
#guard_msgs in #check @syn_b
