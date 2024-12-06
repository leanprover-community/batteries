/-
Copyright (c) 2024 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: François G. Dorais, Quang Dao
-/
import Batteries.Data.List.FinRange
import Batteries.Data.Fin.Basic

namespace Fin

/-! ### dfoldr -/

theorem dfoldr_loop_zero (f : (i : Fin n) → α i.succ → α i.castSucc) (x) :
    dfoldr.loop n α f 0 (Nat.zero_lt_succ n) x = x := rfl

theorem dfoldr_loop_succ (f : (i : Fin n) → α i.succ → α i.castSucc) (h : i < n) (x) :
      dfoldr.loop n α f (i+1) (Nat.add_lt_add_right h 1) x =
        dfoldr.loop n α f i (Nat.lt_add_right 1 h) (f ⟨i, h⟩ x) := rfl

theorem dfoldr_loop (f : (i : Fin (n+1)) → α i.succ → α i.castSucc) (h : i+1 ≤ n+1) (x) :
      dfoldr.loop (n+1) α f (i+1) (Nat.add_lt_add_right h 1) x =
        f 0 (dfoldr.loop n (α ∘ succ) (f ·.succ) i h x) := by
  induction i with
  | zero => rfl
  | succ i ih => exact ih ..

@[simp] theorem dfoldr_zero (f : (i : Fin 0) → α i.succ → α i.castSucc) (x) :
    dfoldr 0 α f x = x := rfl

theorem dfoldr_succ (f : (i : Fin (n+1)) → α i.succ → α i.castSucc) (x) :
    dfoldr (n+1) α f x = f 0 (dfoldr n (α ∘ succ) (f ·.succ) x) := dfoldr_loop ..

theorem dfoldr_succ_last (f : (i : Fin (n+1)) → α i.succ → α i.castSucc) (x) :
    dfoldr (n+1) α f x = dfoldr n (α ∘ castSucc) (f ·.castSucc) (f (last n) x) := by
  induction n with
  | zero => simp only [dfoldr_succ, dfoldr_zero, last, zero_eta]
  | succ n ih => rw [dfoldr_succ, ih (α := α ∘ succ) (f ·.succ), dfoldr_succ]; congr

theorem dfoldr_eq_dfoldrM (f : (i : Fin n) → α i.succ → α i.castSucc) (x) :
    dfoldr n α f x = dfoldrM (m:=Id) n α f x := rfl

theorem dfoldr_eq_foldr (f : Fin n → α → α) (x : α) : dfoldr n (fun _ => α) f x = foldr n f x := by
  induction n with
  | zero => simp only [dfoldr_zero, foldr_zero]
  | succ n ih => simp only [dfoldr_succ, foldr_succ, Function.comp_apply, Function.comp_def, ih]

/-! ### dfoldrM -/

@[simp] theorem dfoldrM_zero [Monad m] (f : (i : Fin 0) → α i.succ → m (α i.castSucc)) (x) :
    dfoldrM 0 α f x = pure x := rfl

theorem dfoldrM_succ [Monad m] (f : (i : Fin (n+1)) → α i.succ → m (α i.castSucc))
    (x) : dfoldrM (n+1) α f x = dfoldrM n (α ∘ succ) (f ·.succ) x >>= f 0 := dfoldr_succ ..

theorem dfoldrM_eq_foldrM [Monad m] [LawfulMonad m] (f : (i : Fin n) → α → m α) (x : α) :
    dfoldrM n (fun _ => α) f x = foldrM n f x := by
  induction n generalizing x with
  | zero => simp only [dfoldrM_zero, foldrM_zero]
  | succ n ih => simp only [dfoldrM_succ, foldrM_succ, Function.comp_def, ih]

/-! ### dfoldl -/

theorem dfoldl_loop_lt (f : ∀ (i : Fin n), α i.castSucc → α i.succ) (h : i < n) (x) :
    dfoldl.loop n α f i (Nat.lt_add_right 1 h) x =
      dfoldl.loop n α f (i+1) (Nat.add_lt_add_right h 1) (f ⟨i, h⟩ x) := by
  rw [dfoldl.loop, dif_pos h]

theorem dfoldl_loop_eq (f : ∀ (i : Fin n), α i.castSucc → α i.succ) (x) :
    dfoldl.loop n α f n (Nat.le_refl _) x = x := by
  rw [dfoldl.loop, dif_neg (Nat.lt_irrefl _), cast_eq]

@[simp] theorem dfoldl_zero (f : (i : Fin 0) → α i.castSucc → α i.succ) (x) :
    dfoldl 0 α f x = x := dfoldl_loop_eq ..

theorem dfoldl_loop (f : (i : Fin (n+1)) → α i.castSucc → α i.succ) (h : i < n+1) (x) :
    dfoldl.loop (n+1) α f i (Nat.lt_add_right 1 h) x =
      dfoldl.loop n (α ∘ succ) (f ·.succ ·) i h (f ⟨i, h⟩ x) := by
  if h' : i < n then
    rw [dfoldl_loop_lt _ h _]
    rw [dfoldl_loop_lt _ h' _, dfoldl_loop]; rfl
  else
    cases Nat.le_antisymm (Nat.le_of_lt_succ h) (Nat.not_lt.1 h')
    rw [dfoldl_loop_lt]
    rw [dfoldl_loop_eq, dfoldl_loop_eq]

theorem dfoldl_succ (f : (i : Fin (n+1)) → α i.castSucc → α i.succ) (x) :
    dfoldl (n+1) α f x = dfoldl n (α ∘ succ) (f ·.succ ·) (f 0 x) := dfoldl_loop ..

theorem dfoldl_succ_last (f : (i : Fin (n+1)) → α i.castSucc → α i.succ) (x) :
    dfoldl (n+1) α f x = f (last n) (dfoldl n (α ∘ castSucc) (f ·.castSucc ·) x) := by
  rw [dfoldl_succ]
  induction n with
  | zero => simp [dfoldl_succ, last]
  | succ n ih => rw [dfoldl_succ, @ih (α ∘ succ) (f ·.succ ·), dfoldl_succ]; congr

theorem dfoldl_eq_foldl (f : Fin n → α → α) (x : α) :
    dfoldl n (fun _ => α) f x = foldl n (fun x i => f i x) x := by
  induction n generalizing x with
  | zero => simp only [dfoldl_zero, foldl_zero]
  | succ n ih =>
    simp only [dfoldl_succ, foldl_succ, Function.comp_apply, Function.comp_def]
    congr; simp only [ih]

/-! ### dfoldlM -/

theorem dfoldlM_loop_lt [Monad m] (f : ∀ (i : Fin n), α i.castSucc → m (α i.succ)) (h : i < n) (x) :
    dfoldlM.loop n α f i (Nat.lt_add_right 1 h) x =
      (f ⟨i, h⟩ x) >>= (dfoldlM.loop n α f (i+1) (Nat.add_lt_add_right h 1)) := by
  rw [dfoldlM.loop, dif_pos h]

theorem dfoldlM_loop_eq [Monad m] (f : ∀ (i : Fin n), α i.castSucc → m (α i.succ)) (x) :
    dfoldlM.loop n α f n (Nat.le_refl _) x = pure x := by
  rw [dfoldlM.loop, dif_neg (Nat.lt_irrefl _), cast_eq]

@[simp] theorem dfoldlM_zero [Monad m] (f : (i : Fin 0) → α i.castSucc → m (α i.succ)) (x) :
    dfoldlM 0 α f x = pure x := dfoldlM_loop_eq ..

theorem dfoldlM_loop [Monad m] (f : (i : Fin (n+1)) → α i.castSucc → m (α i.succ)) (h : i < n+1)
    (x) : dfoldlM.loop (n+1) α f i (Nat.lt_add_right 1 h) x =
      f ⟨i, h⟩ x >>= (dfoldlM.loop n (α ∘ succ) (f ·.succ ·) i h .) := by
  if h' : i < n then
    rw [dfoldlM_loop_lt _ h _]
    congr; funext
    rw [dfoldlM_loop_lt _ h' _, dfoldlM_loop]; rfl
  else
    cases Nat.le_antisymm (Nat.le_of_lt_succ h) (Nat.not_lt.1 h')
    rw [dfoldlM_loop_lt]
    congr; funext
    rw [dfoldlM_loop_eq, dfoldlM_loop_eq]

theorem dfoldlM_succ [Monad m] (f : (i : Fin (n+1)) → α i.castSucc → m (α i.succ)) (x) :
    dfoldlM (n+1) α f x = f 0 x >>= (dfoldlM n (α ∘ succ) (f ·.succ ·) .) :=
  dfoldlM_loop ..

theorem dfoldlM_eq_foldlM [Monad m] (f : (i : Fin n) → α → m α) (x : α) :
    dfoldlM n (fun _ => α) f x = foldlM n (fun x i => f i x) x := by
  induction n generalizing x with
  | zero => simp only [dfoldlM_zero, foldlM_zero]
  | succ n ih =>
    simp only [dfoldlM_succ, foldlM_succ, Function.comp_apply, Function.comp_def]
    congr; ext; simp only [ih]

/-! ### `Fin.fold{l/r}{M}` equals `List.fold{l/r}{M}` -/

theorem foldlM_eq_foldlM_finRange [Monad m] (f : α → Fin n → m α) (x) :
    foldlM n f x = (List.finRange n).foldlM f x := by
  induction n generalizing x with
  | zero => simp
  | succ n ih =>
    rw [foldlM_succ, List.finRange_succ, List.foldlM_cons]
    congr; funext
    rw [List.foldlM_map, ih]

@[deprecated (since := "2024-11-19")]
alias foldlM_eq_foldlM_list := foldlM_eq_foldlM_finRange

theorem foldrM_eq_foldrM_finRange [Monad m] [LawfulMonad m] (f : Fin n → α → m α) (x) :
    foldrM n f x = (List.finRange n).foldrM f x := by
  induction n with
  | zero => simp
  | succ n ih => rw [foldrM_succ, ih, List.finRange_succ, List.foldrM_cons, List.foldrM_map]

@[deprecated (since := "2024-11-19")]
alias foldrM_eq_foldrM_list := foldrM_eq_foldrM_finRange

theorem foldl_eq_foldl_finRange (f : α → Fin n → α) (x) :
    foldl n f x = (List.finRange n).foldl f x := by
  induction n generalizing x with
  | zero => rw [foldl_zero, List.finRange_zero, List.foldl_nil]
  | succ n ih => rw [foldl_succ, ih, List.finRange_succ, List.foldl_cons, List.foldl_map]

@[deprecated (since := "2024-11-19")]
alias foldl_eq_foldl_list := foldl_eq_foldl_finRange

theorem foldr_eq_foldr_finRange (f : Fin n → α → α) (x) :
    foldr n f x = (List.finRange n).foldr f x := by
  induction n with
  | zero => rw [foldr_zero, List.finRange_zero, List.foldr_nil]
  | succ n ih => rw [foldr_succ, ih, List.finRange_succ, List.foldr_cons, List.foldr_map]

@[deprecated (since := "2024-11-19")]
alias foldr_eq_foldr_list := foldr_eq_foldr_finRange
