/-
Copyright (c) 2024 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: François G. Dorais, Quang Dao
-/
module

public import Batteries.Tactic.Alias
public import Batteries.Data.Fin.Basic

@[expose] public section

namespace Fin

/-! ### dfoldrM -/

theorem dfoldrM_loop_zero [Monad m] (f : (i : Fin n) → α i.succ → m (α i.castSucc)) (x) :
    dfoldrM.loop n α f 0 h x = pure x := rfl

theorem dfoldrM_loop_succ [Monad m] (f : (i : Fin n) → α i.succ → m (α i.castSucc)) (x) :
    dfoldrM.loop n α f (i+1) h x = f ⟨i, by omega⟩ x >>= dfoldrM.loop n α f i (by omega) := rfl

theorem dfoldrM_loop [Monad m] [LawfulMonad m] (f : (i : Fin (n+1)) → α i.succ → m (α i.castSucc))
    (x) : dfoldrM.loop (n+1) α f (i+1) h x =
      dfoldrM.loop n (α ∘ succ) (f ·.succ) i (by omega) x >>= f 0 := by
  induction i with
  | zero =>
    rw [dfoldrM_loop_zero, dfoldrM_loop_succ, pure_bind]
    conv => rhs; rw [← bind_pure (f 0 x)]
    rfl
  | succ i ih =>
    rw [dfoldrM_loop_succ, dfoldrM_loop_succ, bind_assoc]
    congr; funext; exact ih ..

@[simp] theorem dfoldrM_zero [Monad m] (f : (i : Fin 0) → α i.succ → m (α i.castSucc)) (x) :
    dfoldrM 0 α f x = pure x := rfl

theorem dfoldrM_succ [Monad m] [LawfulMonad m] (f : (i : Fin (n+1)) → α i.succ → m (α i.castSucc))
    (x) : dfoldrM (n+1) α f x = dfoldrM n (α ∘ succ) (f ·.succ) x >>= f 0 := dfoldrM_loop ..

theorem dfoldrM_eq_foldrM [Monad m] [LawfulMonad m] (f : (i : Fin n) → α → m α) (x) :
    dfoldrM n (fun _ => α) f x = foldrM n f x := by
  induction n with
  | zero => simp only [dfoldrM_zero, foldrM_zero]
  | succ n ih => simp only [dfoldrM_succ, foldrM_succ, Function.comp_def, ih]

theorem dfoldr_eq_dfoldrM (f : (i : Fin n) → α i.succ → α i.castSucc) (x) :
    dfoldr n α f x = dfoldrM (m:=Id) n α f x := rfl

/-! ### dfoldr -/

@[simp] theorem dfoldr_zero (f : (i : Fin 0) → α i.succ → α i.castSucc) (x) :
    dfoldr 0 α f x = x := rfl

theorem dfoldr_succ (f : (i : Fin (n+1)) → α i.succ → α i.castSucc) (x) :
    dfoldr (n+1) α f x = f 0 (dfoldr n (α ∘ succ) (f ·.succ) x) := dfoldrM_succ ..

theorem dfoldr_succ_last {n : Nat} {α : Fin (n+2) → Sort _}
    (f : (i : Fin (n+1)) → α i.succ → α i.castSucc) (x : α (last (n+1))) :
      dfoldr (n+1) α f x = dfoldr n (α ∘ castSucc) (f ·.castSucc) (f (last n) x) := by
  induction n with
  | zero => simp only [dfoldr_succ, dfoldr_zero, last, zero_eta]
  | succ n ih => rw [dfoldr_succ, ih (α := α ∘ succ) (f ·.succ), dfoldr_succ]; congr

theorem dfoldr_eq_foldr (f : (i : Fin n) → α → α) (x) :
    dfoldr n (fun _ => α) f x = foldr n f x := by
  induction n with
  | zero => simp only [dfoldr_zero, foldr_zero]
  | succ n ih => simp only [dfoldr_succ, foldr_succ, Function.comp_def, ih]

/-! ### dfoldlM -/

theorem dfoldlM_loop_lt [Monad m] (f : ∀ (i : Fin n), α i.castSucc → m (α i.succ)) (h : i < n) (x) :
    dfoldlM.loop n α f i (Nat.lt_add_right 1 h) x =
      (f ⟨i, h⟩ x) >>= (dfoldlM.loop n α f (i+1) (Nat.add_lt_add_right h 1)) := by
  rw [dfoldlM.loop, dif_pos h]

theorem dfoldlM_loop_eq [Monad m] (f : ∀ (i : Fin n), α i.castSucc → m (α i.succ)) (x) :
    dfoldlM.loop n α f n (Nat.le_refl _) x = pure x := by
  rw [dfoldlM.loop, dif_neg (Nat.lt_irrefl _), cast_eq]

@[simp] theorem dfoldlM_zero [Monad m] (f : (i : Fin 0) → α i.castSucc → m (α i.succ)) (x) :
    dfoldlM 0 α f x = pure x := rfl

theorem dfoldlM_loop [Monad m] (f : (i : Fin (n+1)) → α i.castSucc → m (α i.succ)) (h : i < n+1)
    (x) : dfoldlM.loop (n+1) α f i (Nat.lt_add_right 1 h) x =
      f ⟨i, h⟩ x >>= (dfoldlM.loop n (α ∘ succ) (f ·.succ ·) i h .) := by
  if h' : i < n then
    rw [dfoldlM_loop_lt _ h _]
    congr; funext
    rw [dfoldlM_loop_lt _ h' _, dfoldlM_loop]; rfl
  else
    cases Nat.le_antisymm (Nat.le_of_lt_succ h) (Nat.not_lt.1 h')
    rw [dfoldlM_loop_lt _ h]
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

/-! ### dfoldl -/

@[simp] theorem dfoldl_zero (f : (i : Fin 0) → α i.castSucc → α i.succ) (x) :
    dfoldl 0 α f x = x := rfl

theorem dfoldl_succ (f : (i : Fin (n+1)) → α i.castSucc → α i.succ) (x) :
    dfoldl (n+1) α f x = dfoldl n (α ∘ succ) (f ·.succ ·) (f 0 x) := dfoldlM_succ ..

theorem dfoldl_succ_last (f : (i : Fin (n+1)) → α i.castSucc → α i.succ) (x) :
    dfoldl (n+1) α f x = f (last n) (dfoldl n (α ∘ castSucc) (f ·.castSucc ·) x) := by
  rw [dfoldl_succ]
  induction n with
  | zero => simp [last]
  | succ n ih => rw [dfoldl_succ, @ih (α ∘ succ) (f ·.succ ·), dfoldl_succ]; congr

theorem dfoldl_eq_dfoldlM (f : (i : Fin n) → α i.castSucc → α i.succ) (x) :
    dfoldl n α f x = dfoldlM (m := Id) n α f x := rfl

theorem dfoldl_eq_foldl (f : Fin n → α → α) (x : α) :
    dfoldl n (fun _ => α) f x = foldl n (fun x i => f i x) x := by
  induction n generalizing x with
  | zero => simp only [dfoldl_zero, foldl_zero]
  | succ n ih =>
    simp only [dfoldl_succ, foldl_succ, Function.comp_apply, Function.comp_def]
    congr; simp only [ih]

/-! ### `Fin.fold{l/r}{M}` equals `List.fold{l/r}{M}` -/

theorem foldl_eq_foldl_finRange (f : α → Fin n → α) (x) :
    foldl n f x = (List.finRange n).foldl f x := by
  induction n generalizing x with
  | zero => rw [foldl_zero, List.finRange_zero, List.foldl_nil]
  | succ n ih => rw [foldl_succ, ih, List.finRange_succ, List.foldl_cons, List.foldl_map]

theorem foldr_eq_foldr_finRange (f : Fin n → α → α) (x) :
    foldr n f x = (List.finRange n).foldr f x := by
  induction n with
  | zero => rw [foldr_zero, List.finRange_zero, List.foldr_nil]
  | succ n ih => rw [foldr_succ, ih, List.finRange_succ, List.foldr_cons, List.foldr_map]
