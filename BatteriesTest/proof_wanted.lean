import Batteries.Util.ProofWanted

/-!
# Tests for `proof_wanted`
-/

/-! No unused variable warnings, even though `x` is only mentioned in the statement. -/
#guard_msgs in proof_wanted no_unused_warning (x : Nat) : x = x

/-! After elaboration, the wanted statement lives in the env as a `ProofWanted`. -/
proof_wanted env_trace : 17 = 37

/--
info: env_trace : ProofWanted (17 = 37)
-/
#guard_msgs in #check @env_trace

/-! ## Bracket references -/

/-! Forward reference via `❰…❱` works: the resulting statement records "if env_trace then …". -/
proof_wanted with_ref :
    (⟨17, by rw [❰env_trace❱]; decide⟩ : Fin 50) = 0

/-! Repeated references to the same bracket share one hypothesis binder. -/
proof_wanted double_ref :
    (⟨17, by rw [❰env_trace❱]; decide⟩ : Fin 50)
      = (⟨17, by rw [❰env_trace❱]; decide⟩ : Fin 50)

/--
info: @double_ref : {h_env_trace : env_trace.Stmt} → ProofWanted (⟨17, ⋯⟩ = ⟨17, ⋯⟩)
-/
#guard_msgs in #check @double_ref

/-! Multiple distinct brackets each get their own hypothesis. -/
proof_wanted other_eq : 5 = 11

proof_wanted two_refs :
    (⟨17, by rw [❰env_trace❱]; decide⟩ : Fin 50)
      = (⟨5, by rw [❰other_eq❱]; decide⟩ : Fin 50)

/-! Two distinct brackets produce two distinct binders, in order of first occurrence. -/
/--
info: @two_refs : {h_env_trace : env_trace.Stmt} → {h_other_eq : other_eq.Stmt} → ProofWanted (⟨17, ⋯⟩ = ⟨5, ⋯⟩)
-/
#guard_msgs in #check @two_refs

/-! ## Parametrised references

`❰foo❱` applied to arguments works when `foo` has its own binders. -/

proof_wanted param_pw (n : Nat) : n = n

proof_wanted ref_param_pw :
    (⟨5, by rw [❰param_pw❱ 5]; decide⟩ : Fin 50) = 0

/--
info: @ref_param_pw : {h_param_pw : ∀ (n : Nat), (param_pw n).Stmt} → ProofWanted (⟨5, ⋯⟩ = 0)
-/
#guard_msgs in #check @ref_param_pw

/-! Implicit binders. The printed `param_imp.Stmt` drops the implicit argument cosmetically; the
underlying type retains it (see `set_option pp.all true`). -/

proof_wanted param_imp {n : Nat} : n = n

proof_wanted ref_param_imp :
    (⟨5, by rw [show (5 : Nat) = 5 from ❰param_imp❱]; decide⟩ : Fin 50) = 0

/--
info: @ref_param_imp : {h_param_imp : ∀ {n : Nat}, param_imp.Stmt} → ProofWanted (⟨5, ⋯⟩ = 0)
-/
#guard_msgs in #check @ref_param_imp

/-! Instance binders. `❰param_inst❱` resolves the instance from context. -/

proof_wanted param_inst [Decidable True] : True

proof_wanted ref_param_inst :
    (⟨0, by have : True := ❰param_inst❱; decide⟩ : Fin 50) = 0

/--
info: @ref_param_inst : {h_param_inst : ∀ [inst : Decidable True], param_inst.Stmt} → ProofWanted (⟨0, ⋯⟩ = 0)
-/
#guard_msgs in #check @ref_param_inst

/-! Multiple dependent binders. -/

proof_wanted param_many (n : Nat) (h : n > 0) : n - 1 < n

proof_wanted ref_param_many :
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
#guard_msgs in proof_wanted bad_unknown : ❰not_declared❱

/-! Referencing a regular `def` (not a `ProofWanted`). -/
private def regular_def : Nat := 0

/--
error: `regular_def` is not a `proof_wanted` declaration (its type doesn't end in `ProofWanted _`)
-/
#guard_msgs in proof_wanted bad_not_pw : ❰regular_def❱

/-! Referencing a hand-rolled `ProofWanted` whose statement isn't a `Prop`. -/
private def fake_pw : ProofWanted Nat := ⟨⟩

/--
error: `fake_pw` is a `ProofWanted`, but its statement is not a proposition
-/
#guard_msgs in proof_wanted bad_not_prop : ❰fake_pw❱

/-! Using `❰…❱` outside `proof_wanted`. -/
/--
error: `❰…❱` may only appear inside the statement of `proof_wanted`
-/
#guard_msgs in example : True := ❰env_trace❱

/-! `❰…❱` in a binder type is rejected explicitly. -/
/--
error: `❰…❱` may not appear inside binder types of `proof_wanted`
-/
#guard_msgs in proof_wanted bad_in_binder (h : ❰env_trace❱) : True

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
#guard_msgs in proof_wanted bad_not_a_prop (x : Nat) : Nat

/-! ## Namespacing -/

namespace N
  proof_wanted ns_foo : 17 = 37

  /-- Bracket resolution works on namespaced names; the generated hypothesis uses just the last
      component of the name. -/
  proof_wanted ns_bar :
      (⟨17, by rw [❰ns_foo❱]; decide⟩ : Fin 50) = 0
end N

/-! ## Soundness

A `proof_wanted` must *not* be usable as a proof of its statement. The placeholder has type
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

/-- And the bracket itself is not a term-level escape hatch: outside `proof_wanted` it errors,
and inside `proof_wanted` it only adds a hypothesis to the recorded statement. So even chained
`proof_wanted`s never produce a real proof, only a wanted theorem of the form "if … then …". -/
example : True := trivial
