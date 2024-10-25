/-
Copyright (c) 2022 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Batteries.Data.Fin.Basic
import Batteries.Data.List.Lemmas
import Batteries.Tactic.Lint.Simp

namespace Fin

attribute [norm_cast] val_last

@[nolint simpNF, simp]
theorem val_ndrec (x : Fin n) (h : m = n) : (h ▸ x).val = x.val := by
  cases h; rfl

/-! ### clamp -/

@[simp] theorem coe_clamp (n m : Nat) : (clamp n m : Nat) = min n m := rfl

/-! ### enum/list -/

@[simp] theorem size_enum (n) : (enum n).size = n := Array.size_ofFn ..

@[simp] theorem enum_zero : (enum 0) = #[] := by simp [enum, Array.ofFn, Array.ofFn.go]

@[simp] theorem getElem_enum (i) (h : i < (enum n).size) : (enum n)[i] = ⟨i, size_enum n ▸ h⟩ :=
  Array.getElem_ofFn ..

@[simp] theorem length_list (n) : (list n).length = n := by simp [list]

@[simp] theorem getElem_list (i : Nat) (h : i < (list n).length) :
    (list n)[i] = cast (length_list n) ⟨i, h⟩ := by
  simp only [list]; rw [← Array.getElem_eq_getElem_toList, getElem_enum, cast_mk]

@[deprecated getElem_list (since := "2024-06-12")]
theorem get_list (i : Fin (list n).length) : (list n).get i = i.cast (length_list n) := by
  simp [getElem_list]

@[simp] theorem list_zero : list 0 = [] := by simp [list]

theorem list_succ (n) : list (n+1) = 0 :: (list n).map Fin.succ := by
  apply List.ext_get; simp; intro i; cases i <;> simp

theorem list_succ_last (n) : list (n+1) = (list n).map castSucc ++ [last n] := by
  rw [list_succ]
  induction n with
  | zero => simp
  | succ n ih =>
    rw [list_succ, List.map_cons castSucc, ih]
    simp [Function.comp_def, succ_castSucc]

theorem list_reverse (n) : (list n).reverse = (list n).map rev := by
  induction n with
  | zero => simp
  | succ n ih =>
    conv => lhs; rw [list_succ_last]
    conv => rhs; rw [list_succ]
    simp [← List.map_reverse, ih, Function.comp_def, rev_succ]

/-! ### foldlM -/

theorem foldlM_loop_lt [Monad m] (f : α → Fin n → m α) (x) (h : i < n) :
    foldlM.loop n f x i = f x ⟨i, h⟩ >>= (foldlM.loop n f . (i+1)) := by
  rw [foldlM.loop, dif_pos h]

theorem foldlM_loop_eq [Monad m] (f : α → Fin n → m α) (x) : foldlM.loop n f x n = pure x := by
  rw [foldlM.loop, dif_neg (Nat.lt_irrefl _)]

theorem foldlM_loop [Monad m] (f : α → Fin (n+1) → m α) (x) (h : i < n+1) :
    foldlM.loop (n+1) f x i = f x ⟨i, h⟩ >>= (foldlM.loop n (fun x j => f x j.succ) . i) := by
  if h' : i < n then
    rw [foldlM_loop_lt _ _ h]
    congr; funext
    rw [foldlM_loop_lt _ _ h', foldlM_loop]; rfl
  else
    cases Nat.le_antisymm (Nat.le_of_lt_succ h) (Nat.not_lt.1 h')
    rw [foldlM_loop_lt]
    congr; funext
    rw [foldlM_loop_eq, foldlM_loop_eq]
termination_by n - i

@[simp] theorem foldlM_zero [Monad m] (f : α → Fin 0 → m α) (x) : foldlM 0 f x = pure x :=
  foldlM_loop_eq ..

theorem foldlM_succ [Monad m] (f : α → Fin (n+1) → m α) (x) :
    foldlM (n+1) f x = f x 0 >>= foldlM n (fun x j => f x j.succ) := foldlM_loop ..

theorem foldlM_eq_foldlM_list [Monad m] (f : α → Fin n → m α) (x) :
    foldlM n f x = (list n).foldlM f x := by
  induction n generalizing x with
  | zero => simp
  | succ n ih =>
    rw [foldlM_succ, list_succ, List.foldlM_cons]
    congr; funext
    rw [List.foldlM_map, ih]

/-! ### foldrM -/

theorem foldrM_loop_zero [Monad m] (f : Fin n → α → m α) (x) :
    foldrM.loop n f ⟨0, Nat.zero_le _⟩ x = pure x := by
  rw [foldrM.loop]

theorem foldrM_loop_succ [Monad m] (f : Fin n → α → m α) (x) (h : i < n) :
    foldrM.loop n f ⟨i+1, h⟩ x = f ⟨i, h⟩ x >>= foldrM.loop n f ⟨i, Nat.le_of_lt h⟩ := by
  rw [foldrM.loop]

theorem foldrM_loop [Monad m] [LawfulMonad m] (f : Fin (n+1) → α → m α) (x) (h : i+1 ≤ n+1) :
    foldrM.loop (n+1) f ⟨i+1, h⟩ x =
      foldrM.loop n (fun j => f j.succ) ⟨i, Nat.le_of_succ_le_succ h⟩ x >>= f 0 := by
  induction i generalizing x with
  | zero =>
    rw [foldrM_loop_zero, foldrM_loop_succ, pure_bind]
    conv => rhs; rw [←bind_pure (f 0 x)]
    congr; funext; exact foldrM_loop_zero ..
  | succ i ih =>
    rw [foldrM_loop_succ, foldrM_loop_succ, bind_assoc]
    congr; funext; exact ih ..

@[simp] theorem foldrM_zero [Monad m] (f : Fin 0 → α → m α) (x) : foldrM 0 f x = pure x :=
  foldrM_loop_zero ..

theorem foldrM_succ [Monad m] [LawfulMonad m] (f : Fin (n+1) → α → m α) (x) :
    foldrM (n+1) f x = foldrM n (fun i => f i.succ) x >>= f 0 := foldrM_loop ..

theorem foldrM_eq_foldrM_list [Monad m] [LawfulMonad m] (f : Fin n → α → m α) (x) :
    foldrM n f x = (list n).foldrM f x := by
  induction n with
  | zero => simp
  | succ n ih => rw [foldrM_succ, ih, list_succ, List.foldrM_cons, List.foldrM_map]

/-! ### foldl -/

theorem foldl_loop_lt (f : α → Fin n → α) (x) (h : i < n) :
    foldl.loop n f x i = foldl.loop n f (f x ⟨i, h⟩) (i+1) := by
  rw [foldl.loop, dif_pos h]

theorem foldl_loop_eq (f : α → Fin n → α) (x) : foldl.loop n f x n = x := by
  rw [foldl.loop, dif_neg (Nat.lt_irrefl _)]

theorem foldl_loop (f : α → Fin (n+1) → α) (x) (h : i < n+1) :
    foldl.loop (n+1) f x i = foldl.loop n (fun x j => f x j.succ) (f x ⟨i, h⟩) i := by
  if h' : i < n then
    rw [foldl_loop_lt _ _ h]
    rw [foldl_loop_lt _ _ h', foldl_loop]; rfl
  else
    cases Nat.le_antisymm (Nat.le_of_lt_succ h) (Nat.not_lt.1 h')
    rw [foldl_loop_lt]
    rw [foldl_loop_eq, foldl_loop_eq]

@[simp] theorem foldl_zero (f : α → Fin 0 → α) (x) : foldl 0 f x = x :=
  foldl_loop_eq ..

theorem foldl_succ (f : α → Fin (n+1) → α) (x) :
    foldl (n+1) f x = foldl n (fun x i => f x i.succ) (f x 0) :=
  foldl_loop ..

theorem foldl_succ_last (f : α → Fin (n+1) → α) (x) :
    foldl (n+1) f x = f (foldl n (f · ·.castSucc) x) (last n) := by
  rw [foldl_succ]
  induction n generalizing x with
  | zero => simp [foldl_succ, Fin.last]
  | succ n ih => rw [foldl_succ, ih (f · ·.succ), foldl_succ]; simp [succ_castSucc]

theorem foldl_eq_foldlM (f : α → Fin n → α) (x) :
    foldl n f x = foldlM (m:=Id) n f x := by
  induction n generalizing x <;> simp [foldl_succ, foldlM_succ, *]

theorem foldl_eq_foldl_list (f : α → Fin n → α) (x) : foldl n f x = (list n).foldl f x := by
  induction n generalizing x with
  | zero => rw [foldl_zero, list_zero, List.foldl_nil]
  | succ n ih => rw [foldl_succ, ih, list_succ, List.foldl_cons, List.foldl_map]

/-! ### foldr -/

theorem foldr_loop_zero (f : Fin n → α → α) (x) :
    foldr.loop n f ⟨0, Nat.zero_le _⟩ x = x := by
  rw [foldr.loop]

theorem foldr_loop_succ (f : Fin n → α → α) (x) (h : i < n) :
    foldr.loop n f ⟨i+1, h⟩ x = foldr.loop n f ⟨i, Nat.le_of_lt h⟩ (f ⟨i, h⟩ x) := by
  rw [foldr.loop]

theorem foldr_loop (f : Fin (n+1) → α → α) (x) (h : i+1 ≤ n+1) :
    foldr.loop (n+1) f ⟨i+1, h⟩ x =
      f 0 (foldr.loop n (fun j => f j.succ) ⟨i, Nat.le_of_succ_le_succ h⟩ x) := by
  induction i generalizing x <;> simp [foldr_loop_zero, foldr_loop_succ, *]

@[simp] theorem foldr_zero (f : Fin 0 → α → α) (x) : foldr 0 f x = x :=
  foldr_loop_zero ..

theorem foldr_succ (f : Fin (n+1) → α → α) (x) :
    foldr (n+1) f x = f 0 (foldr n (fun i => f i.succ) x) := foldr_loop ..

theorem foldr_succ_last (f : Fin (n+1) → α → α) (x) :
    foldr (n+1) f x = foldr n (f ·.castSucc) (f (last n) x) := by
  induction n generalizing x with
  | zero => simp [foldr_succ, Fin.last]
  | succ n ih => rw [foldr_succ, ih (f ·.succ), foldr_succ]; simp [succ_castSucc]

theorem foldr_eq_foldrM (f : Fin n → α → α) (x) :
    foldr n f x = foldrM (m:=Id) n f x := by
  induction n <;> simp [foldr_succ, foldrM_succ, *]

theorem foldr_eq_foldr_list (f : Fin n → α → α) (x) : foldr n f x = (list n).foldr f x := by
  induction n with
  | zero => rw [foldr_zero, list_zero, List.foldr_nil]
  | succ n ih => rw [foldr_succ, ih, list_succ, List.foldr_cons, List.foldr_map]

theorem foldl_rev (f : Fin n → α → α) (x) :
    foldl n (fun x i => f i.rev x) x = foldr n f x := by
  induction n generalizing x with
  | zero => simp
  | succ n ih => rw [foldl_succ, foldr_succ_last, ← ih]; simp [rev_succ]

theorem foldr_rev (f : α → Fin n → α) (x) :
     foldr n (fun i x => f x i.rev) x = foldl n f x := by
  induction n generalizing x with
  | zero => simp
  | succ n ih => rw [foldl_succ_last, foldr_succ, ← ih]; simp [rev_succ]

theorem map_foldr {g : α → β} {f : Fin n → α → α} {f' : Fin n → β → β}
    (h : ∀ i x, g (f i x) = f' i (g x)) (x) : g (foldr n f x) = foldr n f' (g x) := by
  induction n generalizing x with
  | zero => simp
  | succ n ih => simp [foldr_succ, ih, h]

/-! ### sum -/

@[simp] theorem sum_zero [OfNat α (nat_lit 0)] [Add α] (x : Fin 0 → α) :
    Fin.sum x = 0 := by
  simp [Fin.sum]

theorem sum_succ [OfNat α (nat_lit 0)] [Add α] (x : Fin (n + 1) → α) :
    Fin.sum x = x 0 + Fin.sum (x ∘ Fin.succ) := by
  simp [Fin.sum, foldr_succ]

/-! ### prod -/

@[simp] theorem prod_zero [OfNat α (nat_lit 1)] [Mul α] (x : Fin 0 → α) :
    Fin.prod x = 1 := by
  simp [Fin.prod]

theorem prod_succ [OfNat α (nat_lit 1)] [Mul α] (x : Fin (n + 1) → α) :
    Fin.prod x = x 0 * Fin.prod (x ∘ Fin.succ) := by
  simp [Fin.prod, foldr_succ]

/-! ### count -/

@[simp] theorem count_zero (P : Fin 0 → Prop) [DecidablePred P] : Fin.count P = 0 := by
  simp [Fin.count]

theorem count_succ (P : Fin (n + 1) → Prop) [DecidablePred P] : Fin.count P =
    if P 0 then Fin.count (fun i => P i.succ) + 1 else Fin.count (fun i => P i.succ) := by
  split <;> simp [Fin.count, Fin.sum_succ, Nat.one_add, Function.comp_def, *]

theorem count_le (P : Fin n → Prop) [DecidablePred P] : Fin.count P ≤ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [count_succ]
    split
    · simp [ih]
    · apply Nat.le_trans _ (Nat.le_succ n); simp [ih]

/-! ### find? -/

@[simp] theorem find?_zero {P : Fin 0 → Prop} [DecidablePred P] : Fin.find? P = none := by
  simp [Fin.find?]

theorem find?_succ (P : Fin (n+1) → Prop) [DecidablePred P] :
    Fin.find? P = if P 0 then some 0 else (Fin.find? fun i => P i.succ).map Fin.succ := by
  have h (i : Fin n) (v : Option (Fin n)) :
      (if P i.succ then some i else v).map Fin.succ =
        if P i.succ then some i.succ else v.map Fin.succ := by
    intros; split <;> simp
  simp [Fin.find?, foldr_succ, map_foldr h]

theorem find?_prop {P : Fin n → Prop} [DecidablePred P] (h : Fin.find? P = some x) : P x := by
  induction n with
  | zero => simp at h
  | succ n ih =>
    simp [find?_succ] at h
    split at h
    · cases h; assumption
    · simp [Option.map_eq_some] at h
      match h with
      | ⟨i, h', hi⟩ => cases hi; exact ih h'

theorem find?_isSome_of_prop {P : Fin n → Prop} [DecidablePred P] (h : P x) :
    (Fin.find? P).isSome := by
  induction n with
  | zero => nomatch x
  | succ n ih =>
    rw [find?_succ]
    split
    · rfl
    · have hx : x ≠ 0 := by
        intro hx
        rw [hx] at h
        contradiction
      have h : P (x.pred hx).succ := by simp [h]
      rw [Option.isSome_map']
      exact ih h

theorem find?_isSome_iff_exists {P : Fin n → Prop} [DecidablePred P] :
    (Fin.find? P).isSome ↔ ∃ x, P x := by
  constructor
  · intro h
    match heq : Fin.find? P with
    | some x => exists x; exact find?_prop heq
    | none => rw [heq] at h; contradiction
  · intro ⟨_, h⟩
    exact find?_isSome_of_prop h

/-! ### recZeroSuccOn -/

unseal Fin.recZeroSuccOn in
@[simp] theorem recZeroSuccOn_zero {motive : Fin (n+1) → Sort _} (zero : motive 0)
    (succ : (x : Fin n) → motive x.castSucc → motive x.succ) :
    Fin.recZeroSuccOn 0 zero succ = zero := rfl

unseal Fin.recZeroSuccOn in
theorem recZeroSuccOn_succ {motive : Fin (n+1) → Sort _} (x : Fin n)  (zero : motive 0)
    (succ : (x : Fin n) → motive x.castSucc → motive x.succ) :
    Fin.recZeroSuccOn x.succ zero succ = succ x (Fin.recZeroSuccOn x.castSucc zero succ) := rfl

/-! ### casesZeroSuccOn -/

@[simp] theorem casesZeroSuccOn_zero {motive : Fin (n+1) → Sort _} (zero : motive 0)
    (succ : (x : Fin n) → motive x.succ) : Fin.casesZeroSuccOn 0 zero succ = zero := rfl

@[simp] theorem casesZeroSuccOn_succ {motive : Fin (n+1) → Sort _} (x : Fin n)  (zero : motive 0)
    (succ : (x : Fin n) → motive x.succ) : Fin.casesZeroSuccOn x.succ zero succ = succ x := rfl
