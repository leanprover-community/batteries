/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

namespace EStateM

namespace Result

/-- Map a function over an `EStateM.Result`, preserving states and errors. -/
def map {ε σ α β} (f : α → β) (x : Result ε σ α) : Result ε σ β :=
  match x with
  | .ok a s' => .ok (f a) s'
  | .error e s' => .error e s'

@[simp] theorem map_ok {ε σ α β} (f : α → β) (a : α) (s : σ) :
    (Result.ok a s : Result ε σ α).map f = .ok (f a) s := rfl

@[simp] theorem map_error {ε σ α β} (f : α → β) (e : ε) (s : σ) :
    (Result.error e s : Result ε σ α).map f = .error e s := rfl

@[simp] theorem map_eq_ok {ε σ α β} {f : α → β} {x : Result ε σ α} {b : β} {s : σ} :
    x.map f = .ok b s ↔ ∃ a, x = .ok a s ∧ b = f a := by
  cases x <;> simp [and_assoc, and_comm, eq_comm]

@[simp] theorem map_eq_error {ε σ α β} (f : α → β) {x : Result ε σ α} {e : ε} {s : σ} :
    x.map f = .error e s ↔ x = .error e s := by
  cases x <;> simp [eq_comm]

end Result

@[simp] theorem run_map (f : α → β) (x : EStateM ε σ α) :
    (f <$> x).run s = (x.run s).map f := rfl

@[ext] theorem ext {ε σ α} {x y : EStateM ε σ α} (h : ∀ s, x.run s = y.run s) : x = y := by
  funext s
  exact h s

end EStateM
