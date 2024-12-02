/-
Copyright (c) 2022 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Batteries.Data.Fin.Basic
import Batteries.Data.List.Lemmas

namespace Fin

attribute [norm_cast] val_last

/-! ### clamp -/

@[simp] theorem coe_clamp (n m : Nat) : (clamp n m : Nat) = min n m := rfl

/-! ### foldM -/

variable {n : Nat} {α : Fin (n+1) → Type _} [Monad m]
    (f : ∀ (i : Fin n), α i.castSucc → m (α i.succ))

theorem foldM_loop_lt (h : i < n) (x : α ⟨i, Nat.lt_add_right 1 h⟩) :
    foldM.loop n α f i (Nat.lt_add_right 1 h) x =
      (f ⟨i, h⟩ x) >>= (foldM.loop n α f (i+1) (Nat.add_lt_add_right h 1)) := by
  rw [foldM.loop, dif_pos h]

theorem foldM_loop_eq (x : α ⟨n, Nat.le_refl _⟩) :
    foldM.loop n α f n (Nat.le_refl _) x = pure x := by
  rw [foldM.loop, dif_neg (Nat.lt_irrefl _), cast_eq]

@[simp] theorem foldM_zero {α : Fin 1 → Sort _} (f : (i : Fin 0) → α i.castSucc → m (α i.succ))
    (x : α 0) : foldM 0 α f x = pure x :=
  foldM_loop_eq ..

variable {α : Fin (n+2) → Type _} (f : (i : Fin (n+1)) → α i.castSucc → m (α i.succ))

theorem foldM_loop (h : i < n+1) (x : α ⟨i, Nat.lt_add_right 1 h⟩) :
    foldM.loop (n+1) α f i (Nat.lt_add_right 1 h) x =
      f ⟨i, h⟩ x >>= (foldM.loop n (α ∘ succ) (f ·.succ ·) i h .) := by
  if h' : i < n then
    rw [foldM_loop_lt _ h _]
    congr; funext
    rw [foldM_loop_lt _ h' _, foldM_loop]; rfl
  else
    cases Nat.le_antisymm (Nat.le_of_lt_succ h) (Nat.not_lt.1 h')
    rw [foldM_loop_lt]
    congr; funext
    rw [foldM_loop_eq, foldM_loop_eq]

theorem foldM_succ (x) : foldM (n+1) α f x = f 0 x >>= foldM n (α ∘ succ) (f ·.succ ·) :=
  foldM_loop ..

/-- Dependent version `foldM` equals non-dependent version `foldlM` --/
theorem foldM_eq_foldlM {α : Type _} (f : Fin n → α → m α) (x : α) :
    foldM n (fun _ => α) f x = foldlM n (fun x i => f i x) x := by
  induction n generalizing x with
  | zero => simp only [foldM_zero, foldlM_zero]
  | succ n ih =>
    simp only [foldM_succ, foldlM_succ, Function.comp_apply, Function.comp_def]
    congr; ext; simp only [ih]

/-! ### fold -/

variable {α : Fin (n+1) → Sort _} (f : ∀ (i : Fin n), α i.castSucc → α i.succ)

theorem fold_loop_lt (h : i < n) (x : α ⟨i, Nat.lt_add_right 1 h⟩) :
    fold.loop n α f i (Nat.lt_add_right 1 h) x =
      fold.loop n α f (i+1) (Nat.add_lt_add_right h 1) (f ⟨i, h⟩ x) := by
  rw [fold.loop, dif_pos h]

theorem fold_loop_eq (x : α ⟨n, Nat.le_refl _⟩) :
    fold.loop n α f n (Nat.le_refl _) x = x := by
  rw [fold.loop, dif_neg (Nat.lt_irrefl _), cast_eq]

@[simp] theorem fold_zero {α : Fin 1 → Sort _} (f : (i : Fin 0) → α i.castSucc → α i.succ)
    (x : α 0) : fold 0 α f x = x :=
  fold_loop_eq ..

variable {α : Fin (n+2) → Sort _} (f : (i : Fin (n+1)) → α i.castSucc → α i.succ)

theorem fold_loop (h : i < n+1) (x : α ⟨i, Nat.lt_add_right 1 h⟩) :
    fold.loop (n+1) α f i (Nat.lt_add_right 1 h) x =
      fold.loop n (α ∘ succ) (f ·.succ ·) i h (f ⟨i, h⟩ x) := by
  if h' : i < n then
    rw [fold_loop_lt _ h _]
    rw [fold_loop_lt _ h' _, fold_loop]; rfl
  else
    cases Nat.le_antisymm (Nat.le_of_lt_succ h) (Nat.not_lt.1 h')
    rw [fold_loop_lt]
    rw [fold_loop_eq, fold_loop_eq]

theorem fold_succ (x : α 0) : fold (n+1) α f x = fold n (α ∘ succ) (f ·.succ ·) (f 0 x) :=
  fold_loop ..

theorem fold_succ_last (x : α 0) :
    fold (n+1) α f x = f (last n) (fold n (α ∘ castSucc) (f ·.castSucc ·) x) := by
  rw [fold_succ]
  induction n with
  | zero => simp [fold_succ, last]
  | succ n ih => rw [fold_succ, @ih (α ∘ succ) (f ·.succ ·), fold_succ]; congr

theorem fold_eq_foldl {α : Sort _} (f : Fin n → α → α) (x : α) :
    fold n (fun _ => α) f x = foldl n (fun x i => f i x) x := by
  induction n generalizing x with
  | zero => simp only [fold_zero, foldl_zero]
  | succ n ih =>
    simp only [fold_succ, foldl_succ, Function.comp_apply, Function.comp_def]
    congr; simp only [ih]
