/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module
import all Init.Control.EState

@[expose] public section

namespace EStateM

open Backtrackable

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

@[simp] theorem dummySave_apply (s : σ) : EStateM.dummySave s = PUnit.unit := rfl

@[simp] theorem dummyRestore_apply (s : σ) : EStateM.dummyRestore s = Function.const _ s := rfl

@[simp] theorem run_pure (x : α) (s : σ) :
    (pure x : EStateM ε σ α).run s = Result.ok x s := rfl

@[simp] theorem run'_pure (x : α) (s : σ) :
    (pure x : EStateM ε σ α).run' s = some x := rfl

@[simp] theorem run_bind (x : EStateM ε σ α) (f : α → EStateM ε σ β) (s : σ) :
    (x >>= f).run s = match x.run s with
    | .ok a s => (f a).run s
    | .error e s => .error e s := rfl

@[simp] theorem run'_bind (x : EStateM ε σ α) (f : α → EStateM ε σ β) (s : σ) :
    (x >>= f).run' s = match x.run s with
    | .ok a s => (f a).run' s
    | .error _ _ => none := by
  rw [run', run_bind]
  cases x.run s <;> rfl

@[simp] theorem run_map (f : α → β) (x : EStateM ε σ α) (s : σ) :
    (f <$> x).run s = (x.run s).map f := rfl

@[simp] theorem run'_map (f : α → β) (x : EStateM ε σ α) (s : σ) :
    (f <$> x).run' s = Option.map f (x.run' s) := by
  rw [run', run', run_map]
  cases x.run s <;> rfl

theorem run_seq (f : EStateM ε σ (α → β)) (x : EStateM ε σ α) (s : σ) :
    (f <*> x).run s = match f.run s with
    | .ok g s => Result.map g (x.run s)
    | .error e s => .error e s := by
  simp only [seq_eq_bind_map, run_bind, run_map]
  cases f.run s <;> rfl

theorem run'_seq (f : EStateM ε σ (α → β)) (x : EStateM ε σ α) (s : σ) :
    (f <*> x).run' s = match f.run s with
    | .ok g s => Option.map g (x.run' s)
    | .error _ _ => none := by
  simp only [seq_eq_bind_map, run'_bind, run'_map]
  cases f.run s <;> rfl

@[simp] theorem run_seqLeft (x : EStateM ε σ α) (y : EStateM ε σ β) (s : σ) :
    (x <* y).run s = match x.run s with
    | .ok v s => Result.map (fun _ => v) (y.run s)
    | .error e s => .error e s := by
  simp [seqLeft_eq_bind]

@[simp] theorem run'_seqLeft (x : EStateM ε σ α) (y : EStateM ε σ β) (s : σ) :
    (x <* y).run' s = match x.run s with
    | .ok v s => Option.map (fun _ => v) (y.run' s)
    | .error _ _ => none := by
  simp [seqLeft_eq_bind]

@[simp] theorem run_seqRight (x : EStateM ε σ α) (y : EStateM ε σ β) (s : σ) :
    (x *> y).run s = match x.run s with
    | .ok _ s => y.run s
    | .error e s => .error e s := rfl

@[simp] theorem run'_seqRight (x : EStateM ε σ α) (y : EStateM ε σ β) (s : σ) :
    (x *> y).run' s = match x.run s with
    | .ok _ s => y.run' s
    | .error _ _ => none := by
  rw [run', run_seqRight]
  cases x.run s <;> rfl

@[simp] theorem run_get (s : σ) :
    (get : EStateM ε σ σ).run s = Result.ok s s := rfl

@[simp] theorem run'_get (s : σ) :
    (get : EStateM ε σ σ).run' s = some s := rfl

@[simp] theorem run_set (v s : σ) :
    (set v : EStateM ε σ PUnit).run s = Result.ok PUnit.unit v := rfl

@[simp] theorem run'_set (v s : σ) :
    (set v : EStateM ε σ PUnit).run' s = some PUnit.unit := rfl

@[simp] theorem run_modify (f : σ → σ) (s : σ) :
    (modify f : EStateM ε σ PUnit).run s = Result.ok PUnit.unit (f s) := rfl

@[simp] theorem run'_modify (f : σ → σ) (s : σ) :
    (modify f : EStateM ε σ PUnit).run' s = some PUnit.unit := rfl

@[simp] theorem run_modifyGet (f : σ → α × σ) (s : σ) :
    (modifyGet f : EStateM ε σ α).run s = Result.ok (f s).1 (f s).2 := rfl

@[simp] theorem run'_modifyGet (f : σ → α × σ) (s : σ) :
    (modifyGet f : EStateM ε σ α).run' s = some (f s).1 := rfl

@[simp] theorem run_getModify (f : σ → σ) :
    (getModify f : EStateM ε σ σ).run s = Result.ok s (f s) := rfl

@[simp] theorem run'_getModify (f : σ → σ) (s : σ) :
    (getModify f : EStateM ε σ σ).run' s = some s := rfl

@[simp] theorem run_throw (e : ε) (s : σ) :
    (throw e : EStateM ε σ α).run s = Result.error e s := rfl

@[simp] theorem run'_throw (e : ε) (s : σ) :
    (throw e : EStateM ε σ α).run' s = none := rfl

@[simp] theorem run_orElse {δ} [h : Backtrackable δ σ] (x₁ x₂ : EStateM ε σ α) (s : σ) :
    (x₁ <|> x₂).run s = match x₁.run s with
    | .ok x s => .ok x s
    | .error _ s' => x₂.run (restore s' (save s)) := by
  show (EStateM.orElse _ _).run _ = _
  unfold EStateM.orElse
  simp only [EStateM.run]
  match x₁ s with | .ok _ _ => rfl | .error _ _ => simp

@[simp] theorem run'_orElse {δ} [h : Backtrackable δ σ] (x₁ x₂ : EStateM ε σ α) (s : σ) :
    (x₁ <|> x₂).run' s = match x₁.run s with
    | .ok x _ => some x
    | .error _ s' => x₂.run' (restore s' (save s)) := by
  rw [run', run_orElse]
  cases x₁.run s <;> rfl

@[simp] theorem run_tryCatch {δ} [h : Backtrackable δ σ]
    (body : EStateM ε σ α) (handler : ε → EStateM ε σ α) (s : σ) :
    (tryCatch body handler).run s = match body.run s with
    | .ok x s => .ok x s
    | .error e s' => (handler e).run (restore s' (save s)) := by
  show (EStateM.tryCatch _ _).run _ = _
  unfold EStateM.tryCatch
  simp only [EStateM.run]
  cases body s <;> rfl

@[simp] theorem run'_tryCatch {δ} [h : Backtrackable δ σ]
    (body : EStateM ε σ α) (handler : ε → EStateM ε σ α) (s : σ) :
    (tryCatch body handler).run' s = match body.run s with
    | .ok x _ => some x
    | .error e s' => (handler e).run' (restore s' (save s)) := by
  rw [run', run_tryCatch]
  cases body.run s <;> rfl

@[simp] theorem run_adaptExcept (f : ε → ε) (x : EStateM ε σ α) (s : σ) :
    (adaptExcept f x).run s = match x.run s with
    | .ok x s => .ok x s
    | .error e s => .error (f e) s := by
  show (EStateM.adaptExcept _ _).run _ = _
  unfold EStateM.adaptExcept
  simp only [EStateM.run]
  cases x s <;> rfl

@[simp] theorem run'_adaptExcept (f : ε → ε) (x : EStateM ε σ α) (s : σ) :
    (adaptExcept f x).run' s = x.run' s := by
  rw [run', run', run_adaptExcept]
  cases x.run s <;> rfl

@[simp] theorem run_tryFinally' (x : EStateM ε σ α)
    (h : Option α → EStateM ε σ β) (s : σ) : (tryFinally' x h).run s = match x.run s with
    | .ok a s => match (h (some a)).run s with
      | .ok b s => Result.ok (a, b) s
      | .error e s => Result.error e s
    | .error e₁ s => match (h none).run s with
      | .ok _ s => Result.error e₁ s
      | .error e₂ s => Result.error e₂ s := rfl

@[simp] theorem run'_tryFinally' (x : EStateM ε σ α)
    (h : Option α → EStateM ε σ β) (s : σ) :
    (tryFinally' x h).run' s = match x.run s with
    | .ok a s => Option.map (a, ·) ((h (some a)).run' s)
    | .error _ _ => none := by
  simp [run', run_tryFinally']
  match x.run s with
  | .ok a s => simp only; cases (h (some a)).run s <;> rfl
  | .error e s => simp only; cases (h none).run s <;> rfl

@[simp] theorem run_fromStateM (x : StateM σ α) (s : σ) :
    (fromStateM x : EStateM ε σ α).run s =
    Result.ok (x.run s).1 (x.run s).2 := (rfl)

@[simp] theorem run'_fromStateM (x : StateM σ α) (s : σ) :
    (fromStateM x : EStateM ε σ α).run' s = some (x.run' s) := (rfl)

@[ext] theorem ext {ε σ α} {x y : EStateM ε σ α} (h : ∀ s, x.run s = y.run s) : x = y := by
  funext s
  exact h s

end EStateM
