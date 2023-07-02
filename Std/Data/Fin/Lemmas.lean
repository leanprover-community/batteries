/-
Copyright (c) 2022 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Std.Data.Fin.Basic
import Std.Data.Nat.Lemmas
import Std.Tactic.Ext
import Std.Tactic.Simpa
import Std.Tactic.NormCast.Lemmas

namespace Fin

/-- If you actually have an element of `Fin n`, then the `n` is always positive -/
theorem size_pos (i : Fin n) : 0 < n := Nat.lt_of_le_of_lt (Nat.zero_le _) i.2

theorem mod_def (a m : Fin n) : a % m = Fin.mk ((a % m) % n) (Nat.mod_lt _ a.size_pos) := rfl

theorem mul_def (a b : Fin n) : a * b = Fin.mk ((a * b) % n) (Nat.mod_lt _ a.size_pos) := rfl

theorem sub_def (a b : Fin n) : a - b = Fin.mk ((a + (n - b)) % n) (Nat.mod_lt _ a.size_pos) := rfl

theorem size_pos' : ∀ [Nonempty (Fin n)], 0 < n | ⟨i⟩ => i.size_pos

@[simp] theorem is_lt (a : Fin n) : (a : Nat) < n := a.2

theorem pos_iff_nonempty {n : Nat} : 0 < n ↔ Nonempty (Fin n) :=
  ⟨fun h => ⟨⟨0, h⟩⟩, fun ⟨i⟩ => i.pos⟩

/-! ### coercions and constructions -/

@[simp] protected theorem eta (a : Fin n) (h : a < n) : (⟨a, h⟩ : Fin n) = a := by cases a; rfl

@[ext] theorem ext {a b : Fin n} (h : (a : Nat) = b) : a = b := eq_of_val_eq h

theorem val_inj {a b : Fin n} : a.1 = b.1 ↔ a = b := ⟨Fin.eq_of_val_eq, Fin.val_eq_of_eq⟩

theorem ext_iff {a b : Fin n} : a = b ↔ a.1 = b.1 := val_inj.symm

theorem val_ne_iff {a b : Fin n} : a.1 ≠ b.1 ↔ a ≠ b := not_congr val_inj

theorem exists_iff {p : Fin n → Prop} : (∃ i, p i) ↔ ∃ i h, p ⟨i, h⟩ :=
  ⟨fun ⟨⟨i, hi⟩, hpi⟩ => ⟨i, hi, hpi⟩, fun ⟨i, hi, hpi⟩ => ⟨⟨i, hi⟩, hpi⟩⟩

theorem forall_iff {p : Fin n → Prop} : (∀ i, p i) ↔ ∀ i h, p ⟨i, h⟩ :=
  ⟨fun h i hi => h ⟨i, hi⟩, fun h ⟨i, hi⟩ => h i hi⟩

protected theorem mk.inj_iff {n a b : Nat} {ha : a < n} {hb : b < n} :
    (⟨a, ha⟩ : Fin n) = ⟨b, hb⟩ ↔ a = b := ext_iff

theorem val_mk {m n : Nat} (h : m < n) : (⟨m, h⟩ : Fin n).val = m := rfl

theorem eq_mk_iff_val_eq {a : Fin n} {k : Nat} {hk : k < n} :
    a = ⟨k, hk⟩ ↔ (a : Nat) = k := ext_iff

theorem mk_val (i : Fin n) : (⟨i, i.isLt⟩ : Fin n) = i := Fin.eta ..

@[simp] theorem ofNat'_zero_val : (Fin.ofNat' 0 h).val = 0 := Nat.zero_mod _

@[simp] theorem mod_val (a b : Fin n) : (a % b).val = a.val % b.val :=
  Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.mod_le ..) a.2)

@[simp] theorem div_val (a b : Fin n) : (a / b).val = a.val / b.val :=
  Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.div_le_self ..) a.2)

@[simp] theorem modn_val (a : Fin n) (b : Nat) : (a.modn b).val = a.val % b :=
  Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.mod_le ..) a.2)

theorem ite_val {n : Nat} {c : Prop} [Decidable c] {x : c → Fin n} (y : ¬c → Fin n) :
    (if h : c then x h else y h).val = if h : c then (x h).val else (y h).val := by
  by_cases c <;> simp [*]

theorem dite_val {n : Nat} {c : Prop} [Decidable c] {x y : Fin n} :
    (if c then x else y).val = if c then x.val else y.val := by
  by_cases c <;> simp [*]

/-! ### order -/

theorem le_def {a b : Fin n} : a ≤ b ↔ a.1 ≤ b.1 := .rfl

theorem lt_def {a b : Fin n} : a < b ↔ a.1 < b.1 := .rfl

@[simp] protected theorem not_le {a b : Fin n} : ¬ a ≤ b ↔ b < a := Nat.not_le

@[simp] protected theorem not_lt {a b : Fin n} : ¬ a < b ↔ b ≤ a := Nat.not_lt

protected theorem ne_of_lt {a b : Fin n} (h : a < b) : a ≠ b := Fin.ne_of_val_ne (Nat.ne_of_lt h)

protected theorem ne_of_gt {a b : Fin n} (h : a < b) : b ≠ a := Fin.ne_of_val_ne (Nat.ne_of_gt h)

theorem is_le (i : Fin (n + 1)) : i ≤ n := Nat.le_of_lt_succ i.is_lt

@[simp] theorem is_le' {a : Fin n} : a ≤ n := Nat.le_of_lt a.is_lt

theorem mk_lt_of_lt_val {b : Fin n} {a : Nat} (h : a < b) :
    (⟨a, Nat.lt_trans h b.is_lt⟩ : Fin n) < b := h

theorem mk_le_of_le_val {b : Fin n} {a : Nat} (h : a ≤ b) :
    (⟨a, Nat.lt_of_le_of_lt h b.is_lt⟩ : Fin n) ≤ b := h

@[simp] theorem mk_le_mk {x y : Nat} {hx hy} : (⟨x, hx⟩ : Fin n) ≤ ⟨y, hy⟩ ↔ x ≤ y := .rfl

@[simp] theorem mk_lt_mk {x y : Nat} {hx hy} : (⟨x, hx⟩ : Fin n) < ⟨y, hy⟩ ↔ x < y := .rfl

@[simp] theorem val_zero (n : Nat) : (0 : Fin (n + 1)).1 = 0 := rfl

theorem zero_lt_one : (0 : Fin (n + 2)) < 1 := Nat.zero_lt_one

@[simp] theorem not_lt_zero (a : Fin (n + 1)) : ¬a < 0 := fun.

theorem eq_zero_or_eq_succ {n : Nat} : ∀ i : Fin (n + 1), i = 0 ∨ ∃ j : Fin n, i = j.succ
  | 0 => .inl rfl
  | ⟨j + 1, h⟩ => .inr ⟨⟨j, Nat.lt_of_succ_lt_succ h⟩, rfl⟩

theorem eq_succ_of_ne_zero {n : Nat} {i : Fin (n + 1)} (hi : i ≠ 0) : ∃ j : Fin n, i = j.succ :=
  (eq_zero_or_eq_succ i).resolve_left hi

@[simp] theorem val_rev (i : Fin n) : rev i = n - (i + 1) := rfl

@[simp] theorem rev_rev (i : Fin n) : rev (rev i) = i := ext <| by
  rw [val_rev, val_rev, ← Nat.sub_sub, Nat.sub_sub_self (by exact i.2), Nat.add_sub_cancel]

@[simp] theorem rev_le_rev {i j : Fin n} : rev i ≤ rev j ↔ j ≤ i := by
  simp only [le_def, val_rev, Nat.sub_le_sub_iff_left (Nat.succ_le.2 j.is_lt)]
  exact Nat.succ_le_succ_iff

@[simp] theorem rev_inj {i j : Fin n} : rev i = rev j ↔ i = j :=
  ⟨fun h => by simpa using congrArg rev h, congrArg _⟩

theorem rev_eq {n a : Nat} (i : Fin (n + 1)) (h : n = a + i) :
    rev i = ⟨a, Nat.lt_succ_of_le (h ▸ Nat.le_add_right ..)⟩ := by
  ext; dsimp
  conv => lhs; congr; rw [h]
  rw [Nat.add_assoc, Nat.add_sub_cancel]

@[simp] theorem rev_lt_rev {i j : Fin n} : rev i < rev j ↔ j < i := by
  rw [← Fin.not_le, ← Fin.not_le, rev_le_rev]

@[simp, norm_cast] theorem val_last (n : Nat) : last n = n := rfl

theorem le_last (i : Fin (n + 1)) : i ≤ last n := Nat.le_of_lt_succ i.is_lt

theorem last_pos : (0 : Fin (n + 2)) < last (n + 1) := Nat.succ_pos _

theorem eq_last_of_not_lt {i : Fin (n + 1)} (h : ¬(i : Nat) < n) : i = last n :=
  ext <| Nat.le_antisymm (le_last i) (Nat.not_lt.1 h)

theorem val_lt_last {i : Fin (n + 1)} : i ≠ last n → (i : Nat) < n :=
  Decidable.not_imp_comm.1 eq_last_of_not_lt

/-! ### addition, numerals, and coercion from Nat -/

@[simp] theorem val_one (n : Nat) : (1 : Fin (n + 2)).val = 1 := rfl

@[simp] theorem mk_one : (⟨1, Nat.succ_lt_succ (Nat.succ_pos n)⟩ : Fin (n + 2)) = (1 : Fin _) := rfl

theorem add_def (a b : Fin n) : a + b = Fin.mk ((a + b) % n) (Nat.mod_lt _ a.size_pos) := rfl

theorem val_add (a b : Fin n) : (a + b).val = (a.val + b.val) % n := rfl

theorem val_add_one_of_lt {n : Nat} {i : Fin n.succ} (h : i < last _) : (i + 1).1 = i + 1 := by
  match n with
  | 0 => cases h
  | n+1 => rw [val_add, val_one, Nat.mod_eq_of_lt (by exact Nat.succ_lt_succ h)]

@[simp] theorem last_add_one : ∀ n, last n + 1 = 0
  | 0 => rfl
  | n + 1 => by ext; rw [val_add, val_zero, val_last, val_one, Nat.mod_self]

theorem val_add_one {n : Nat} (i : Fin (n + 1)) :
    ((i + 1 : Fin (n + 1)) : Nat) = if i = last _ then (0 : Nat) else i + 1 := by
  match Nat.eq_or_lt_of_le (le_last i) with
  | .inl h => cases Fin.eq_of_val_eq h; simp
  | .inr h => simpa [Fin.ne_of_lt h] using val_add_one_of_lt h

@[simp] theorem val_two {n : Nat} : (2 : Fin (n + 3)).val = 2 := rfl

theorem add_one_pos (i : Fin (n + 1)) (h : i < Fin.last n) : (0 : Fin (n + 1)) < i + 1 := by
  match n with
  | 0 => cases h
  | n+1 =>
    rw [Fin.lt_def, val_last, ← Nat.add_lt_add_iff_right 1] at h
    rw [Fin.lt_def, val_add, val_zero, val_one, Nat.mod_eq_of_lt h]
    exact Nat.zero_lt_succ _

theorem one_pos : (0 : Fin (n + 2)) < 1 := Nat.succ_pos 0

theorem zero_ne_one : (0 : Fin (n + 2)) ≠ 1 := Fin.ne_of_lt one_pos

/-! ### succ and casts into larger Fin types -/

@[simp] theorem val_succ (j : Fin n) : (j.succ : Nat) = j + 1 := by cases j; simp [Fin.succ]

@[simp] theorem succ_pos (a : Fin n) : (0 : Fin (n + 1)) < a.succ := by
  simp [Fin.lt_def, Nat.succ_pos]

@[simp] theorem succ_le_succ_iff {a b : Fin n} : a.succ ≤ b.succ ↔ a ≤ b := Nat.succ_le_succ_iff

@[simp] theorem succ_lt_succ_iff {a b : Fin n} : a.succ < b.succ ↔ a < b := Nat.succ_lt_succ_iff

@[simp] theorem succ_inj {a b : Fin n} : a.succ = b.succ ↔ a = b := by
  refine ⟨fun h => ext ?_, congrArg _⟩
  apply Nat.le_antisymm <;> exact succ_le_succ_iff.1 (h ▸ Nat.le_refl _)

theorem succ_ne_zero {n} : ∀ k : Fin n, Fin.succ k ≠ 0
  | ⟨k, _⟩, heq => Nat.succ_ne_zero k <| ext_iff.1 heq

@[simp] theorem succ_zero_eq_one : Fin.succ (0 : Fin (n + 1)) = 1 := rfl

/-- Version of `succ_one_eq_two` to be used by `dsimp` -/
@[simp] theorem succ_one_eq_two : Fin.succ (1 : Fin (n + 2)) = 2 := rfl

@[simp] theorem succ_mk (n i : Nat) (h : i < n) :
    Fin.succ ⟨i, h⟩ = ⟨i + 1, Nat.succ_lt_succ h⟩ := rfl

theorem mk_succ_pos (i : Nat) (h : i < n) :
    (0 : Fin (n + 1)) < ⟨i.succ, Nat.add_lt_add_right h 1⟩ := by
  rw [lt_def, val_zero]; exact Nat.succ_pos i

theorem one_lt_succ_succ (a : Fin n) : (1 : Fin (n + 2)) < a.succ.succ := by
  let n+1 := n
  rw [← succ_zero_eq_one, succ_lt_succ_iff]; exact succ_pos a

@[simp] theorem add_one_lt_iff {n : Nat} {k : Fin (n + 2)} : k + 1 < k ↔ k = last _ := by
  simp only [lt_def, val_add, val_last, ext_iff]
  let ⟨k, hk⟩ := k
  match Nat.eq_or_lt_of_le (Nat.le_of_lt_succ hk) with
  | .inl h => cases h; simp [Nat.succ_pos]
  | .inr hk' => simp [Nat.ne_of_lt hk', Nat.mod_eq_of_lt (Nat.succ_lt_succ hk'), Nat.le_succ]

@[simp] theorem add_one_le_iff {n : Nat} {k : Fin (n + 1)} : k + 1 ≤ k ↔ k = last _ := by
  cases n
  -- Porting note: added `haveI`
  · haveI : Subsingleton (Fin (0 + 1)) := by
      convert_to Subsingleton (Fin 1)
      infer_instance
    simp [Subsingleton.elim (k + 1) k, Subsingleton.elim (Fin.last _) k]
  rw [← not_iff_not, ← add_one_lt_iff, lt_iff_le_and_ne, not_and']
  refine' ⟨fun h _ => h, fun h => h _⟩
  rw [Ne.def, ext_iff, val_add_one]
  split_ifs with hk <;> simp [hk, @eq_comm Nat 0]

@[simp]
theorem last_le_iff {n : Nat} {k : Fin (n + 1)} : last n ≤ k ↔ k = last n :=
  top_le_iff

@[simp]
theorem lt_add_one_iff {n : Nat} {k : Fin (n + 1)} : k < k + 1 ↔ k < last n := by
  rw [← not_iff_not]
  simp

@[simp]
theorem le_zero_iff {n : Nat} [NeZero n] {k : Fin n} : k ≤ 0 ↔ k = 0 :=
  ⟨fun h => Fin.eq_of_veq $ by rw [Nat.eq_zero_of_le_zero h]; rfl, by rintro rfl; exact le_refl _⟩

theorem succ_succ_ne_one (a : Fin n) : Fin.succ (Fin.succ a) ≠ 1 :=
  ne_of_gt (one_lt_succ_succ a)

/-- `castLT i h` embeds `i` into a `Fin` where `h` proves it belongs into.  -/
def castLT (i : Fin m) (h : i.1 < n) : Fin n :=
  ⟨i.1, h⟩

@[simp]
theorem coe_castLT (i : Fin m) (h : i.1 < n) : (castLT i h : Nat) = i :=
  rfl

@[simp]
theorem castLT_mk (i n m : Nat) (hn : i < n) (hm : i < m) : castLT ⟨i, hn⟩ hm = ⟨i, hm⟩ :=
  rfl

/-- `castLE h i` embeds `i` into a larger `Fin` type.  -/
def castLE (h : n ≤ m) : Fin n ↪o Fin m :=
  (OrderEmbedding.ofStrictMono fun a => castLT a (lt_of_lt_of_le a.2 h)) fun _ _ h => h

@[simp]
theorem coe_castLE (h : n ≤ m) (i : Fin n) : (castLE h i : Nat) = i :=
  rfl

@[simp]
theorem castLE_mk (i n m : Nat) (hn : i < n) (h : n ≤ m) :
    castLE h ⟨i, hn⟩ = ⟨i, lt_of_lt_of_le hn h⟩ :=
  rfl

@[simp]
theorem castLE_zero {n m : Nat} (h : n.succ ≤ m.succ) : castLE h 0 = 0 := by simp [eq_iff_veq]

@[simp]
theorem range_castLE {n k : Nat} (h : n ≤ k) : Set.range (castLE h) = { i : Fin k | (i : Nat) < n } :=
  Set.ext fun x => ⟨fun ⟨y, hy⟩ => hy ▸ y.2, fun hx => ⟨⟨x, hx⟩, Fin.ext rfl⟩⟩

@[simp]
theorem coe_of_injective_castLE_symm {n k : Nat} (h : n ≤ k) (i : Fin k) (hi) :
    ((Equiv.ofInjective _ (castLE h).injective).symm ⟨i, hi⟩ : Nat) = i := by
  rw [← coe_castLE]
  exact congr_arg Fin.val (Equiv.apply_ofInjective_symm _ _)

@[simp]
theorem castLE_succ {m n : Nat} (h : m + 1 ≤ n + 1) (i : Fin m) :
    castLE h i.succ = (castLE (Nat.succ_le_succ_iff.mp h) i).succ := by simp [Fin.eq_iff_veq]

@[simp]
theorem castLE_castLE {k m n} (km : k ≤ m) (mn : m ≤ n) (i : Fin k) :
    Fin.castLE mn (Fin.castLE km i) = Fin.castLE (km.trans mn) i :=
  Fin.ext (by simp only [coe_castLE])

@[simp]
theorem castLE_comp_castLE {k m n} (km : k ≤ m) (mn : m ≤ n) :
    Fin.castLE mn ∘ Fin.castLE km = Fin.castLE (km.trans mn) :=
  funext (castLE_castLE km mn)

/-- `cast eq i` embeds `i` into an equal `Fin` type, see also `Equiv.finCongr`. -/
def cast (eq : n = m) : Fin n ≃o Fin m where
  toEquiv := ⟨castLE eq.le, castLE eq.symm.le, fun _ => eq_of_veq rfl, fun _ => eq_of_veq rfl⟩
  map_rel_iff' := Iff.rfl

@[simp]
theorem symm_cast (h : n = m) : (cast h).symm = cast h.symm := by simp

theorem coe_cast (h : n = m) (i : Fin n) : (cast h i : Nat) = i := by simp

@[simp]
theorem cast_zero {n' : Nat} [NeZero n] {h : n = n'} : cast h (0 : Fin n) =
    by { haveI : NeZero n' := by {rw [← h]; infer_instance}; exact 0} :=
  ext rfl

@[simp]
theorem cast_last {n' : Nat} {h : n + 1 = n' + 1} : cast h (last n) = last n' :=
  ext (by rw [coe_cast, val_last, val_last, Nat.succ_injective h])

@[simp]
theorem cast_mk (h : n = m) (i : Nat) (hn : i < n) :
    cast h ⟨i, hn⟩ = ⟨i, lt_of_lt_of_le hn h.le⟩ := by
  ext
  simp

@[simp]
theorem cast_trans {k : Nat} (h : n = m) (h' : m = k) {i : Fin n} :
    cast h' (cast h i) = cast (Eq.trans h h') i := by
  ext
  simp

@[simp]
theorem cast_refl (h : n = n := rfl) : cast h = OrderIso.refl (Fin n) := by
  ext
  simp

theorem castLE_of_eq {m n : Nat} (h : m = n) {h' : m ≤ n} :
    (castLE h' : Fin m → Fin n) = Fin.cast h :=
  funext fun _ => by ext; simp

/-- While in many cases `Fin.cast` is better than `Equiv.cast`/`cast`, sometimes we want to apply
a generic theorem about `cast`. -/
theorem cast_to_equiv (h : n = m) : (cast h).toEquiv = Equiv.cast (h ▸ rfl) := by
  subst h
  simp

/-- While in many cases `Fin.cast` is better than `Equiv.cast`/`cast`, sometimes we want to apply
a generic theorem about `cast`. -/
theorem cast_eq_cast (h : n = m) : (cast h : Fin n → Fin m) = cast (h ▸ rfl) := by
  subst h
  ext
  simp

/-- `castAdd m i` embeds `i : Fin n` in `Fin (n+m)`. See also `Fin.natAdd` and `Fin.addNat`. -/
def castAdd (m) : Fin n ↪o Fin (n + m) :=
  castLE <| Nat.le_add_right n m

@[simp]
theorem coe_castAdd (m : Nat) (i : Fin n) : (castAdd m i : Nat) = i :=
  rfl

@[simp]
theorem castAdd_zero : (castAdd 0 : Fin n → Fin (n + 0)) = cast rfl := by
  ext
  simp only [Nat.add_zero, cast_refl, OrderIso.refl_apply]
  rfl

theorem castAdd_lt {m : Nat} (n : Nat) (i : Fin m) : (castAdd n i : Nat) < m := by
  simp

@[simp]
theorem castAdd_mk (m : Nat) (i : Nat) (h : i < n) : castAdd m ⟨i, h⟩ = ⟨i, Nat.lt_add_right i n m h⟩ :=
  rfl

@[simp]
theorem castAdd_castLT (m : Nat) (i : Fin (n + m)) (hi : i.val < n) :
    castAdd m (castLT i hi) = i := by
  ext
  simp

@[simp]
theorem castLT_castAdd (m : Nat) (i : Fin n) : castLT (castAdd m i) (castAdd_lt m i) = i := by
  ext
  simp

/-- For rewriting in the reverse direction, see `Fin.cast_castAdd_left`. -/
theorem castAdd_cast {n n' : Nat} (m : Nat) (i : Fin n') (h : n' = n) :
    castAdd m (Fin.cast h i) = Fin.cast (congr_arg (. + m) h) (castAdd m i) :=
  ext rfl

theorem cast_castAdd_left {n n' m : Nat} (i : Fin n') (h : n' + m = n + m) :
    cast h (castAdd m i) = castAdd m (cast (add_right_cancel h) i) := by
  ext
  simp

@[simp]
theorem cast_castAdd_right {n m m' : Nat} (i : Fin n) (h : n + m' = n + m) :
    cast h (castAdd m' i) = castAdd m i := by
  ext
  simp

theorem castAdd_castAdd {m n p : Nat} (i : Fin m) :
    castAdd p (castAdd n i) = cast (add_assoc _ _ _).symm (castAdd (n + p) i) := by
  ext
  simp

/-- The cast of the successor is the successor of the cast. See `Fin.succ_cast_eq` for rewriting in
the reverse direction. -/
@[simp]
theorem cast_succ_eq {n' : Nat} (i : Fin n) (h : n.succ = n'.succ) :
    cast h i.succ = (cast (Nat.succ.inj h) i).succ :=
  ext <| by simp

theorem succ_cast_eq {n' : Nat} (i : Fin n) (h : n = n') :
    (cast h i).succ = cast (by rw [h]) i.succ :=
  ext <| by simp

/-- `castSucc i` embeds `i : Fin n` in `Fin (n+1)`. -/
def castSucc : Fin n ↪o Fin (n + 1) :=
  castAdd 1

@[simp]
theorem coe_castSucc (i : Fin n) : (Fin.castSucc i : Nat) = i :=
  rfl

@[simp]
theorem castSucc_mk (n i : Nat) (h : i < n) : castSucc ⟨i, h⟩ = ⟨i, Nat.lt.step h⟩ :=
  rfl

@[simp]
theorem cast_castSucc {n' : Nat} {h : n + 1 = n' + 1} {i : Fin n} :
    cast h (castSucc i) = castSucc (cast (Nat.succ_injective h) i) := by
  ext
  simp only [coe_cast, coe_castSucc]

theorem castSucc_lt_succ (i : Fin n) : Fin.castSucc i < i.succ :=
  lt_iff_val_lt_val.2 <| by simp only [coe_castSucc, val_succ, Nat.lt_succ_self]

theorem le_castSucc_iff {i : Fin (n + 1)} {j : Fin n} : i ≤ Fin.castSucc j ↔ i < j.succ := by
  simpa [lt_iff_val_lt_val, le_iff_val_le_val] using Nat.succ_le_succ_iff.symm

theorem castSucc_lt_iff_succ_le {n : Nat} {i : Fin n} {j : Fin (n + 1)} :
    Fin.castSucc i < j ↔ i.succ ≤ j := by
  simpa only [lt_iff_val_lt_val, le_iff_val_le_val, val_succ, Fin.coe_castSucc] using
    Nat.lt_iff_add_one_le

@[simp]
theorem succ_last (n : Nat) : (last n).succ = last n.succ :=
  rfl

@[simp]
theorem succ_eq_last_succ {n : Nat} (i : Fin n.succ) : i.succ = last (n + 1) ↔ i = last n := by
  rw [← succ_last, (succ_injective _).eq_iff]

@[simp]
theorem castSucc_castLT (i : Fin (n + 1)) (h : (i : Nat) < n) : castSucc (castLT i h) = i :=
  Fin.eq_of_veq rfl

@[simp]
theorem castLT_castSucc {n : Nat} (a : Fin n) (h : (a : Nat) < n) : castLT (castSucc a) h = a := by
  cases a; rfl

--@[simp] Porting note: simp can prove it
theorem castSucc_lt_castSucc_iff {a b : Fin n} : Fin.castSucc a < Fin.castSucc b ↔ a < b :=
  (@castSucc n).lt_iff_lt

theorem castSucc_injective (n : Nat) : Injective (@Fin.castSucc n) :=
  (castSucc : Fin n ↪o _).injective

theorem castSucc_inj {a b : Fin n} : castSucc a = castSucc b ↔ a = b :=
  (castSucc_injective n).eq_iff

theorem castSucc_lt_last (a : Fin n) : castSucc a < last n :=
  lt_iff_val_lt_val.mpr a.is_lt

@[simp]
theorem castSucc_zero [NeZero n] : castSucc (0 : Fin n) = 0 :=
  ext rfl

@[simp]
theorem castSucc_one {n : Nat} : castSucc (1 : Fin (n + 2)) = 1 :=
  rfl

/-- `castSucc i` is positive when `i` is positive -/
theorem castSucc_pos [NeZero n] {i : Fin n} (h : 0 < i) : 0 < castSucc i := by
  simpa [lt_iff_val_lt_val] using h

@[simp]
theorem castSucc_eq_zero_iff [NeZero n] (a : Fin n) : castSucc a = 0 ↔ a = 0 :=
  Fin.ext_iff.trans <| (Fin.ext_iff.trans <| by simp).symm

theorem castSucc_ne_zero_iff [NeZero n] (a : Fin n) : castSucc a ≠ 0 ↔ a ≠ 0 :=
  not_iff_not.mpr <| castSucc_eq_zero_iff a

theorem castSucc_fin_succ (n : Nat) (j : Fin n) : castSucc (Fin.succ j) = Fin.succ (castSucc j) := by
  simp [Fin.ext_iff]

@[norm_cast, simp]
theorem coe_eq_castSucc {a : Fin n} : (a : Fin (n + 1)) = castSucc a := by
  ext
  exact val_cast_of_lt (Nat.lt.step a.is_lt)

@[simp]
theorem coeSucc_eq_succ {a : Fin n} : (castSucc a) + 1 = a.succ := by
  cases n
  · exact @finZeroElim (fun _ => _) a
  · simp [a.is_lt, eq_iff_veq, add_def, Nat.mod_eq_of_lt]

theorem lt_succ {a : Fin n} : castSucc a < a.succ := by
  rw [castSucc, lt_iff_val_lt_val, coe_castAdd, val_succ]
  exact lt_add_one a.val

@[simp]
theorem range_castSucc {n : Nat} : Set.range (castSucc : Fin n → Fin n.succ) =
    ({ i | (i : Nat) < n } : Set (Fin n.succ)) :=
  range_castLE le_self_add

theorem exists_castSucc_eq {n : Nat} {i : Fin (n + 1)} : (∃ j, castSucc j = i) ↔ i ≠ last n :=
  ⟨fun ⟨j, hj⟩ => hj ▸ j.castSucc_lt_last.ne, fun hi => ⟨i.castLT $ Fin.val_lt_last hi, rfl⟩⟩

@[simp]
theorem coe_of_injective_castSucc_symm {n : Nat} (i : Fin n.succ) (hi) :
    ((Equiv.ofInjective castSucc (castSucc_injective _)).symm ⟨i, hi⟩ : Nat) = i := by
  rw [← coe_castSucc]
  exact congr_arg val (Equiv.apply_ofInjective_symm _ _)

theorem succ_castSucc {n : Nat} (i : Fin n) : i.castSucc.succ = castSucc i.succ :=
  Fin.ext (by simp)

/-- `addNat m i` adds `m` to `i`, generalizes `Fin.succ`. -/
def addNat (m) : Fin n ↪o Fin (n + m) :=
  (OrderEmbedding.ofStrictMono fun i => ⟨(i : Nat) + m, add_lt_add_right i.2 _⟩) fun i j h =>
    add_lt_add_right (show i.val < j.val from h) _

@[simp]
theorem coe_addNat (m : Nat) (i : Fin n) : (addNat m i : Nat) = i + m :=
  rfl

@[simp]
theorem addNat_one {i : Fin n} : addNat 1 i = i.succ := by
  ext
  rw [coe_addNat, val_succ]

theorem le_coe_addNat (m : Nat) (i : Fin n) : m ≤ addNat m i :=
  Nat.le_add_left _ _

@[simp]
theorem addNat_mk (n i : Nat) (hi : i < m) : addNat n ⟨i, hi⟩ = ⟨i + n, add_lt_add_right hi n⟩ :=
  rfl

@[simp]
theorem cast_addNat_zero {n n' : Nat} (i : Fin n) (h : n + 0 = n') :
    cast h (addNat 0 i) = cast ((add_zero _).symm.trans h) i :=
  ext <| add_zero _

/-- For rewriting in the reverse direction, see `Fin.cast_addNat_left`. -/
theorem addNat_cast {n n' m : Nat} (i : Fin n') (h : n' = n) :
    addNat m (cast h i) = cast (congr_arg (. + m) h) (addNat m i) :=
  ext rfl

theorem cast_addNat_left {n n' m : Nat} (i : Fin n') (h : n' + m = n + m) :
    cast h (addNat m i) = addNat m (cast (add_right_cancel h) i) := by
  ext
  simp

@[simp]
theorem cast_addNat_right {n m m' : Nat} (i : Fin n) (h : n + m' = n + m) :
    cast h (addNat m' i) = addNat m i :=
  ext <| (congr_arg ((· + ·) (i : Nat)) (add_left_cancel h) : _)

/-- `natAdd n i` adds `n` to `i` "on the left". -/
def natAdd (n) {m} : Fin m ↪o Fin (n + m) :=
  (OrderEmbedding.ofStrictMono fun i => ⟨n + (i : Nat), add_lt_add_left i.2 _⟩) fun i j h =>
    add_lt_add_left (show i.val < j.val from h) _

@[simp]
theorem coe_natAdd (n : Nat) {m : Nat} (i : Fin m) : (natAdd n i : Nat) = n + i :=
  rfl

@[simp]
theorem natAdd_mk (n i : Nat) (hi : i < m) : natAdd n ⟨i, hi⟩ = ⟨n + i, add_lt_add_left hi n⟩ :=
  rfl

theorem le_coe_natAdd (m : Nat) (i : Fin n) : m ≤ natAdd m i :=
  Nat.le_add_right _ _

theorem natAdd_zero {n : Nat} : Fin.natAdd 0 = (Fin.cast (zero_add n).symm).toRelEmbedding := by
  ext
  simp

/-- For rewriting in the reverse direction, see `Fin.cast_natAdd_right`. -/
theorem natAdd_cast {n n' : Nat} (m : Nat) (i : Fin n') (h : n' = n) :
    natAdd m (cast h i) = cast (congr_arg _ h) (natAdd m i) := by
  ext
  simp

theorem cast_natAdd_right {n n' m : Nat} (i : Fin n') (h : m + n' = m + n) :
    cast h (natAdd m i) = natAdd m (cast (add_left_cancel h) i) := by
  ext
  simp

@[simp]
theorem cast_natAdd_left {n m m' : Nat} (i : Fin n) (h : m' + n = m + n) :
    cast h (natAdd m' i) = natAdd m i :=
  ext <| (congr_arg (· + (i : Nat)) (add_right_cancel h) : _)

theorem castAdd_natAdd (p m : Nat) {n : Nat} (i : Fin n) :
    castAdd p (natAdd m i) = cast (add_assoc _ _ _).symm (natAdd m (castAdd p i)) := by
  ext
  simp

theorem natAdd_castAdd (p m : Nat) {n : Nat} (i : Fin n) :
    natAdd m (castAdd p i) = cast (add_assoc _ _ _) (castAdd p (natAdd m i)) := by
  ext
  simp

theorem natAdd_natAdd (m n : Nat) {p : Nat} (i : Fin p) :
    natAdd m (natAdd n i) = cast (add_assoc _ _ _) (natAdd (m + n) i) :=
  ext <| (add_assoc _ _ _).symm

@[simp]
theorem cast_natAdd_zero {n n' : Nat} (i : Fin n) (h : 0 + n = n') :
    cast h (natAdd 0 i) = cast ((zero_add _).symm.trans h) i :=
  ext <| zero_add _

@[simp]
theorem cast_natAdd (n : Nat) {m : Nat} (i : Fin m) : cast (add_comm _ _) (natAdd n i) = addNat n i :=
  ext <| add_comm _ _

@[simp]
theorem cast_addNat {n : Nat} (m : Nat) (i : Fin n) : cast (add_comm _ _) (addNat m i) = natAdd m i :=
  ext <| add_comm _ _

@[simp]
theorem natAdd_last {m n : Nat} : natAdd n (last m) = last (n + m) :=
  rfl

theorem natAdd_castSucc {m n : Nat} {i : Fin m} : natAdd n (castSucc i) = castSucc (natAdd n i) :=
  rfl

end Succ

section Pred

/-!
### pred
-/


-- Porting note: taken from lean3port
/-- Predecessor -/
def pred {n : Nat} : ∀ i : Fin (n + 1), i ≠ 0 → Fin n
  | ⟨a, h₁⟩, h₂ =>
    ⟨a.pred,
      haveI : a ≠ 0 := by
        have aux₁ := vne_of_ne h₂
        dsimp at aux₁
        exact aux₁
      Nat.pred_lt_pred this h₁⟩

@[simp]
theorem coe_pred (j : Fin (n + 1)) (h : j ≠ 0) : (j.pred h : Nat) = j - 1 := by
  cases j
  rfl

@[simp]
theorem succ_pred : ∀ (i : Fin (n + 1)) (h : i ≠ 0), (i.pred h).succ = i
  | ⟨0, h⟩, hi => by simp only [mk_zero, ne_eq, not_true] at hi
  | ⟨n + 1, h⟩, hi => rfl

@[simp]
theorem pred_succ (i : Fin n) {h : i.succ ≠ 0} : i.succ.pred h = i := by
  cases i
  rfl

theorem pred_eq_iff_eq_succ {n : Nat} (i : Fin (n + 1)) (hi : i ≠ 0) (j : Fin n) :
    i.pred hi = j ↔ i = j.succ :=
  ⟨fun h => by simp only [← h, Fin.succ_pred], fun h => by simp only [h, Fin.pred_succ]⟩

--Porting note: removing @[simp]. `pred_mk_succ'` has `simp` attribute instead
theorem pred_mk_succ (i : Nat) (h : i < n + 1) :
    Fin.pred ⟨i + 1, add_lt_add_right h 1⟩ (ne_of_vne (_root_.ne_of_gt (mk_succ_pos i h))) =
      ⟨i, h⟩ := by
  simp only [ext_iff, coe_pred, add_tsub_cancel_right]

--Porting note: new theorem
@[simp]
theorem pred_mk_succ' (i : Nat) (h₁ : i + 1 < n + 1 + 1) (h₂) :
    Fin.pred ⟨i + 1, h₁⟩ h₂ = ⟨i, Nat.lt_of_succ_lt_succ h₁⟩ :=
  pred_mk_succ i _

-- This is not a simp theorem by default, because `pred_mk_succ` is nicer when it applies.
theorem pred_mk {n : Nat} (i : Nat) (h : i < n + 1) (w) : Fin.pred ⟨i, h⟩ w =
    ⟨i - 1, by
      rwa [tsub_lt_iff_right (Nat.succ_le_of_lt <| Nat.pos_of_ne_zero
        (by simpa using Fin.vne_of_ne w))]⟩ :=
  rfl

@[simp]
theorem pred_le_pred_iff {n : Nat} {a b : Fin n.succ} {ha : a ≠ 0} {hb : b ≠ 0} :
    a.pred ha ≤ b.pred hb ↔ a ≤ b := by rw [← succ_le_succ_iff, succ_pred, succ_pred]

@[simp]
theorem pred_lt_pred_iff {n : Nat} {a b : Fin n.succ} {ha : a ≠ 0} {hb : b ≠ 0} :
    a.pred ha < b.pred hb ↔ a < b := by rw [← succ_lt_succ_iff, succ_pred, succ_pred]

@[simp]
theorem pred_inj : ∀ {a b : Fin (n + 1)} {ha : a ≠ 0} {hb : b ≠ 0}, a.pred ha = b.pred hb ↔ a = b
  | ⟨0, _⟩, _, ha, _ => by simp only [mk_zero, ne_eq, not_true] at ha
  | ⟨i + 1, _⟩, ⟨0, _⟩, _, hb => by simp only [mk_zero, ne_eq, not_true] at hb
  | ⟨i + 1, hi⟩, ⟨j + 1, hj⟩, ha, hb => by simp [Fin.eq_iff_veq]

@[simp]
theorem pred_one {n : Nat} : Fin.pred (1 : Fin (n + 2)) (Ne.symm (ne_of_lt one_pos)) = 0 := by
  ext
  simp

theorem pred_add_one (i : Fin (n + 2)) (h : (i : Nat) < n + 1) :
    pred (i + 1) (_root_.ne_of_gt (by exact
      (add_one_pos _ (lt_iff_val_lt_val.2 h)))) = castLT i h := by
  rw [ext_iff, coe_pred, coe_castLT, val_add, val_one, mod_eq_of_lt, add_tsub_cancel_right]
  exact add_lt_add_right h 1

/-- `subNat i h` subtracts `m` from `i`, generalizes `Fin.pred`. -/
def subNat (m) (i : Fin (n + m)) (h : m ≤ (i : Nat)) : Fin n :=
  ⟨(i : Nat) - m, by
    rw [tsub_lt_iff_right h]
    exact i.is_lt⟩

@[simp]
theorem coe_subNat (i : Fin (n + m)) (h : m ≤ i) : (i.subNat m h : Nat) = i - m :=
  rfl

@[simp]
theorem subNat_mk {i : Nat} (h₁ : i < n + m) (h₂ : m ≤ i) :
    subNat m ⟨i, h₁⟩ h₂ = ⟨i - m, (tsub_lt_iff_right h₂).2 h₁⟩ :=
  rfl

@[simp]
theorem pred_castSucc_succ (i : Fin n) :
    pred (castSucc i.succ) (ne_of_gt (castSucc_pos i.succ_pos)) = castSucc i := by
  simp [eq_iff_veq]

@[simp]
theorem addNat_subNat {i : Fin (n + m)} (h : m ≤ i) : addNat m (subNat m i h) = i :=
  ext <| tsub_add_cancel_of_le h

@[simp]
theorem subNat_addNat (i : Fin n) (m : Nat) (h : m ≤ addNat m i := le_coe_addNat m i) :
    subNat m (addNat m i) h = i :=
  ext <| add_tsub_cancel_right (i : Nat) m

@[simp]
theorem natAdd_subNat_cast {i : Fin (n + m)} (h : n ≤ i) :
    natAdd n (subNat n (cast (add_comm _ _) i) h) = i := by simp [← cast_addNat]

end Pred

section DivMod

/-- Compute `i / n`, where `n` is a `Nat` and inferred the type of `i`. -/
def divNat (i : Fin (m * n)) : Fin m :=
  ⟨i / n, Nat.div_lt_of_lt_mul <| mul_comm m n ▸ i.prop⟩

@[simp]
theorem coe_divNat (i : Fin (m * n)) : (i.divNat : Nat) = i / n :=
  rfl

/-- Compute `i % n`, where `n` is a `Nat` and inferred the type of `i`. -/
def modNat (i : Fin (m * n)) : Fin n :=
  ⟨i % n, Nat.mod_lt _ <| pos_of_mul_pos_right i.pos m.zero_le⟩

@[simp]
theorem coe_modNat (i : Fin (m * n)) : (i.modNat : Nat) = i % n :=
  rfl

end DivMod

section Rec

/-!
### recursion and induction principles
-/


/-- Define `C n i` by induction on `i : Fin n` interpreted as `(0 : Fin (n - i)).succ.succ…`.
This function has two arguments: `H0 n` defines `0`-th element `C (n+1) 0` of an `(n+1)`-tuple,
and `Hs n i` defines `(i+1)`-st element of `(n+1)`-tuple based on `n`, `i`, and `i`-th element
of `n`-tuple. -/
@[elab_as_elim]
def succRec {C : ∀ n, Fin n → Sort _} (H0 : ∀ n, C (n.succ) (0 : Fin (n + 1)))
    (Hs : ∀ n i, C n i → C n.succ i.succ) : ∀ {n : Nat} (i : Fin n), C n i
  | 0, i => i.elim0
  | Nat.succ n, ⟨0, _⟩ => by rw [mk_zero]; exact H0 n
  | Nat.succ _, ⟨Nat.succ i, h⟩ => Hs _ _ (succRec H0 Hs ⟨i, lt_of_succ_lt_succ h⟩)

/-- Define `C n i` by induction on `i : Fin n` interpreted as `(0 : Fin (n - i)).succ.succ…`.
This function has two arguments: `H0 n` defines `0`-th element `C (n+1) 0` of an `(n+1)`-tuple,
and `Hs n i` defines `(i+1)`-st element of `(n+1)`-tuple based on `n`, `i`, and `i`-th element
of `n`-tuple.

A version of `Fin.succRec` taking `i : Fin n` as the first argument. -/
@[elab_as_elim]
def succRecOn {n : Nat} (i : Fin n) {C : ∀ n, Fin n → Sort _} (H0 : ∀ n, C (n + 1) 0)
    (Hs : ∀ n i, C n i → C (Nat.succ n) i.succ) : C n i :=
  i.succRec H0 Hs

@[simp]
theorem succRecOn_zero {C : ∀ n, Fin n → Sort _} {H0 Hs} (n) :
    @Fin.succRecOn (n + 1) 0 C H0 Hs = H0 n := by
  cases n <;> rfl

@[simp]
theorem succRecOn_succ {C : ∀ n, Fin n → Sort _} {H0 Hs} {n} (i : Fin n) :
    @Fin.succRecOn (n + 1) i.succ C H0 Hs = Hs n i (Fin.succRecOn i H0 Hs) := by cases i; rfl

/-- Define `C i` by induction on `i : Fin (n + 1)` via induction on the underlying `Nat` value.
This function has two arguments: `h0` handles the base case on `C 0`,
and `hs` defines the inductive step using `C i.castSucc`.
-/
@[elab_as_elim]
def induction {C : Fin (n + 1) → Sort _} (h0 : C 0)
    (hs : ∀ i : Fin n, C (castSucc i) → C i.succ) :
    ∀ i : Fin (n + 1), C i := by
  rintro ⟨i, hi⟩
  induction' i with i IH
  · rwa [Fin.mk_zero]
  · refine' hs ⟨i, lt_of_succ_lt_succ hi⟩ _
    exact IH (lt_of_succ_lt hi)

--Porting note: This proof became a lot more complicated
@[simp]
theorem induction_zero {C : Fin (n + 1) → Sort _} : ∀ (h0 : C 0)
    (hs : ∀ i : Fin n, C (castSucc i) → C i.succ),
    (induction h0 hs : ∀ i : Fin (n + 1), C i) 0 = h0 :=
  have : ⟨0, Nat.zero_lt_succ n⟩ = (0 : Fin (n + 1)) := by simp only [mk_zero]
  Eq.recOn (motive := fun (i : Fin (n + 1)) (h : ⟨0, Nat.zero_lt_succ n⟩ = i) =>
      ∀ (h0 : C i) (hs : ∀ i : Fin n, C (castSucc i) → C i.succ),
        (show ∀ i : Fin (n + 1), C i from induction
          (by simp [← h] at h0; exact h0) hs) i = h0)
    this
    (by intros h0 _; simp [induction])

@[simp]
theorem induction_succ {C : Fin (n + 1) → Sort _} (h0 : C 0)
    (hs : ∀ i : Fin n, C (castSucc i) → C i.succ) (i : Fin n) :
    (induction h0 hs : ∀ i : Fin (n+1), C i) i.succ = hs i (induction h0 hs (castSucc i)) :=
  by cases i; rfl

/-- Define `C i` by induction on `i : Fin (n + 1)` via induction on the underlying `Nat` value.
This function has two arguments: `h0` handles the base case on `C 0`,
and `hs` defines the inductive step using `C i.castSucc`.

A version of `Fin.induction` taking `i : Fin (n + 1)` as the first argument.
-/
@[elab_as_elim]
def inductionOn (i : Fin (n + 1)) {C : Fin (n + 1) → Sort _} (h0 : C 0)
    (hs : ∀ i : Fin n, C (castSucc i) → C i.succ) : C i :=
  induction h0 hs i

/-- Define `f : Π i : Fin n.succ, C i` by separately handling the cases `i = 0` and
`i = j.succ`, `j : Fin n`. -/
@[elab_as_elim]
def cases {C : Fin (n + 1) → Sort _} (H0 : C 0) (Hs : ∀ i : Fin n, C i.succ) :
    ∀ i : Fin (n + 1), C i :=
  induction H0 fun i _ => Hs i

@[simp]
theorem cases_zero {n} {C : Fin (n + 1) → Sort _} {H0 Hs} : @Fin.cases n C H0 Hs 0 = H0 := by
  cases n <;> rfl

@[simp]
theorem cases_succ {n} {C : Fin (n + 1) → Sort _} {H0 Hs} (i : Fin n) :
    @Fin.cases n C H0 Hs i.succ = Hs i := by cases i; rfl

@[simp]
theorem cases_succ' {n} {C : Fin (n + 1) → Sort _} {H0 Hs} {i : Nat} (h : i + 1 < n + 1) :
    @Fin.cases n C H0 Hs ⟨i.succ, h⟩ = Hs ⟨i, lt_of_succ_lt_succ h⟩ := by cases i <;> rfl

theorem forall_fin_succ {P : Fin (n + 1) → Prop} : (∀ i, P i) ↔ P 0 ∧ ∀ i : Fin n, P i.succ :=
  ⟨fun H => ⟨H 0, fun _ => H _⟩, fun ⟨H0, H1⟩ i => Fin.cases H0 H1 i⟩

theorem exists_fin_succ {P : Fin (n + 1) → Prop} : (∃ i, P i) ↔ P 0 ∨ ∃ i : Fin n, P i.succ :=
  ⟨fun ⟨i, h⟩ => Fin.cases Or.inl (fun i hi => Or.inr ⟨i, hi⟩) i h, fun h =>
    (h.elim fun h => ⟨0, h⟩) fun ⟨i, hi⟩ => ⟨i.succ, hi⟩⟩

theorem forall_fin_one {p : Fin 1 → Prop} : (∀ i, p i) ↔ p 0 :=
  @Unique.forall_iff (Fin 1) _ p

theorem exists_fin_one {p : Fin 1 → Prop} : (∃ i, p i) ↔ p 0 :=
  @Unique.exists_iff (Fin 1) _ p

theorem forall_fin_two {p : Fin 2 → Prop} : (∀ i, p i) ↔ p 0 ∧ p 1 :=
  forall_fin_succ.trans <| and_congr_right fun _ => forall_fin_one

theorem exists_fin_two {p : Fin 2 → Prop} : (∃ i, p i) ↔ p 0 ∨ p 1 :=
  exists_fin_succ.trans <| or_congr_right exists_fin_one

theorem fin_two_eq_of_eq_zero_iff {a b : Fin 2} (h : a = 0 ↔ b = 0) : a = b := by
  revert a b
  simp [forall_fin_two]

/--
Define `C i` by reverse induction on `i : Fin (n + 1)` via induction on the underlying `Nat` value.
This function has two arguments: `hlast` handles the base case on `C (Fin.last n)`,
and `hs` defines the inductive step using `C i.succ`, inducting downwards.
-/
@[elab_as_elim]
def reverseInduction {C : Fin (n + 1) → Sort _} (hlast : C (Fin.last n))
    (hs : ∀ i : Fin n, C i.succ → C (castSucc i)) (i : Fin (n + 1)) : C i :=
  if hi : i = Fin.last n then _root_.cast (congr_arg C hi.symm) hlast
  else
    let j : Fin n := ⟨i, lt_of_le_of_ne (Nat.le_of_lt_succ i.2) fun h => hi (Fin.ext h)⟩
    have _ : n - i < n + 1 - i :=
      lt_of_eq_of_lt (Nat.add_sub_add_right ..).symm
        (Nat.sub_lt_sub_left i.2 (Nat.lt_succ_self i))
    have hi : i = Fin.castSucc j := Fin.ext rfl
    _root_.cast (congr_arg C hi.symm) (hs _ (reverseInduction hlast hs j.succ))
termination_by _ => n + 1 - i

@[simp]
theorem reverse_induction_last {n : Nat} {C : Fin (n + 1) → Sort _} (h0 : C (Fin.last n))
    (hs : ∀ i : Fin n, C i.succ → C (castSucc i)) :
    (reverseInduction h0 hs (Fin.last n) : C (Fin.last n)) = h0 := by
  rw [reverseInduction] ; simp

@[simp]
theorem reverse_induction_castSucc {n : Nat} {C : Fin (n + 1) → Sort _} (h0 : C (Fin.last n))
    (hs : ∀ i : Fin n, C i.succ → C (castSucc i)) (i : Fin n) :
    (reverseInduction h0 hs (castSucc i) :
    C (castSucc i)) = hs i (reverseInduction h0 hs i.succ) := by
  rw [reverseInduction, dif_neg (_root_.ne_of_lt (Fin.castSucc_lt_last i))]
  cases i
  rfl

/-- Define `f : Π i : Fin n.succ, C i` by separately handling the cases `i = Fin.last n` and
`i = j.castSucc`, `j : Fin n`. -/
@[elab_as_elim]
def lastCases {n : Nat} {C : Fin (n + 1) → Sort _} (hlast : C (Fin.last n))
    (hcast : ∀ i : Fin n, C (castSucc i)) (i : Fin (n + 1)) : C i :=
  reverseInduction hlast (fun i _ => hcast i) i

@[simp]
theorem lastCases_last {n : Nat} {C : Fin (n + 1) → Sort _} (hlast : C (Fin.last n))
    (hcast : ∀ i : Fin n, C (castSucc i)) :
    (Fin.lastCases hlast hcast (Fin.last n) : C (Fin.last n)) = hlast :=
  reverse_induction_last _ _

@[simp]
theorem lastCases_castSucc {n : Nat} {C : Fin (n + 1) → Sort _} (hlast : C (Fin.last n))
    (hcast : ∀ i : Fin n, C (castSucc i)) (i : Fin n) :
    (Fin.lastCases hlast hcast (Fin.castSucc i) : C (Fin.castSucc i)) = hcast i :=
  reverse_induction_castSucc _ _ _

/-- Define `f : Π i : Fin (m + n), C i` by separately handling the cases `i = castAdd n i`,
`j : Fin m` and `i = natAdd m j`, `j : Fin n`. -/
@[elab_as_elim]
def addCases {m n : Nat} {C : Fin (m + n) → Sort u} (hleft : ∀ i, C (castAdd n i))
    (hright : ∀ i, C (natAdd m i)) (i : Fin (m + n)) : C i :=
  if hi : (i : Nat) < m then (castAdd_castLT n i hi) ▸ (hleft (castLT i hi))
  else (natAdd_subNat_cast (le_of_not_lt hi)) ▸ (hright _)

@[simp]
theorem addCases_left {m n : Nat} {C : Fin (m + n) → Sort _} (hleft : ∀ i, C (castAdd n i))
    (hright : ∀ i, C (natAdd m i)) (i : Fin m) :
    addCases hleft hright (Fin.castAdd n i) = hleft i := by
  cases' i with i hi
  rw [addCases, dif_pos (castAdd_lt _ _)]
  rfl

@[simp]
theorem addCases_right {m n : Nat} {C : Fin (m + n) → Sort _} (hleft : ∀ i, C (castAdd n i))
    (hright : ∀ i, C (natAdd m i)) (i : Fin n) : addCases hleft hright (natAdd m i) = hright i := by
  have : ¬(natAdd m i : Nat) < m := (le_coe_natAdd _ _).not_lt
  rw [addCases, dif_neg this]
  refine' eq_of_heq ((eq_rec_heq _ _).trans _)
  congr 1
  simp

end Rec

theorem liftFun_iff_succ {α : Type _} (r : α → α → Prop) [IsTrans α r] {f : Fin (n + 1) → α} :
    ((· < ·) ⇒ r) f f ↔ ∀ i : Fin n, r (f (castSucc i)) (f i.succ) := by
  constructor
  · intro H i
    exact H i.castSucc_lt_succ
  · refine' fun H i => Fin.induction _ _
    · exact fun h => (h.not_le (zero_le i)).elim
    · intro j ihj hij
      rw [← le_castSucc_iff] at hij
      rcases hij.eq_or_lt with (rfl | hlt)
      exacts [H j, _root_.trans (ihj hlt) (H j)]

/-- A function `f` on `Fin (n + 1)` is strictly monotone if and only if `f i < f (i + 1)`
for all `i`. -/
theorem strictMono_iff_lt_succ {α : Type _} [Preorder α] {f : Fin (n + 1) → α} :
    StrictMono f ↔ ∀ i : Fin n, f (castSucc i) < f i.succ :=
  liftFun_iff_succ (· < ·)

/-- A function `f` on `Fin (n + 1)` is monotone if and only if `f i ≤ f (i + 1)` for all `i`. -/
theorem monotone_iff_le_succ {α : Type _} [Preorder α] {f : Fin (n + 1) → α} :
    Monotone f ↔ ∀ i : Fin n, f (castSucc i) ≤ f i.succ :=
  monotone_iff_forall_lt.trans <| liftFun_iff_succ (· ≤ ·)

/-- A function `f` on `Fin (n + 1)` is strictly antitone if and only if `f (i + 1) < f i`
for all `i`. -/
theorem strictAnti_iff_succ_lt {α : Type _} [Preorder α] {f : Fin (n + 1) → α} :
    StrictAnti f ↔ ∀ i : Fin n, f i.succ < f (castSucc i) :=
  liftFun_iff_succ (· > ·)

/-- A function `f` on `Fin (n + 1)` is antitone if and only if `f (i + 1) ≤ f i` for all `i`. -/
theorem antitone_iff_succ_le {α : Type _} [Preorder α] {f : Fin (n + 1) → α} :
    Antitone f ↔ ∀ i : Fin n, f i.succ ≤ f (castSucc i) :=
  antitone_iff_forall_lt.trans <| liftFun_iff_succ (· ≥ ·)

section AddGroup

open Nat Int

/-- Negation on `Fin n` -/
instance neg (n : Nat) : Neg (Fin n) :=
  ⟨fun a => ⟨(n - a) % n, Nat.mod_lt _ a.pos⟩⟩

/-- Abelian group structure on `Fin n`. -/
instance addCommGroup (n : Nat) [NeZero n] : AddCommGroup (Fin n) :=
  { Fin.addCommMonoid n, Fin.neg n with
    add_left_neg := fun ⟨a, ha⟩ =>
      Fin.ext <|
        _root_.trans (Nat.mod_add_mod _ _ _) <| by
          rw [Fin.val_zero, tsub_add_cancel_of_le, Nat.mod_self]
          exact le_of_lt ha
    sub_eq_add_neg := fun ⟨a, ha⟩ ⟨b, hb⟩ =>
      Fin.ext <| show (a + (n - b)) % n = (a + (n - b) % n) % n by simp
    sub := Fin.sub }

protected theorem coe_neg (a : Fin n) : ((-a : Fin n) : Nat) = (n - a) % n :=
  rfl

protected theorem coe_sub (a b : Fin n) : ((a - b : Fin n) : Nat) = (a + (n - b)) % n := by
  cases a; cases b; rfl

theorem fin_one_eq_zero (a : Fin 1) : a = 0 := by rw [Subsingleton.elim a 0]

@[simp]
theorem coe_fin_one (a : Fin 1) : (a : Nat) = 0 := by simp [Subsingleton.elim a 0]

@[simp]
theorem coe_neg_one : ↑(-1 : Fin (n + 1)) = n := by
  cases n
  · simp
  rw [Fin.coe_neg, Fin.val_one, Nat.succ_sub_one, Nat.mod_eq_of_lt]
  constructor

theorem coe_sub_one {n} (a : Fin (n + 1)) : ↑(a - 1) = if a = 0 then n else a - 1 := by
  cases n
  · simp
  split_ifs with h
  · simp [h]
  rw [sub_eq_add_neg, val_add_eq_ite, coe_neg_one, if_pos, add_comm, add_tsub_add_eq_tsub_left]
  conv_rhs => rw [add_comm]
  rw [add_le_add_iff_left, Nat.one_le_iff_ne_zero]
  rwa [Fin.ext_iff] at h

theorem coe_sub_iff_le {n : Nat} {a b : Fin n} : (↑(a - b) : Nat) = a - b ↔ b ≤ a := by
  cases n; · exact @finZeroElim (fun _ => _) a
  rw [le_iff_val_le_val, Fin.coe_sub, ← add_tsub_assoc_of_le b.is_lt.le a]
  cases' le_or_lt (b : Nat) a with h h
  · simp [← tsub_add_eq_add_tsub h, val_fin_le.mp h,
      Nat.mod_eq_of_lt ((Nat.sub_le _ _).trans_lt a.is_lt)]
  · rw [Nat.mod_eq_of_lt, tsub_eq_zero_of_le h.le, tsub_eq_zero_iff_le, ← not_iff_not]
    · simpa [b.is_lt.trans_le le_add_self] using h
    · rwa [tsub_lt_iff_left (b.is_lt.le.trans le_add_self), add_lt_add_iff_right]

theorem coe_sub_iff_lt {n : Nat} {a b : Fin n} : (↑(a - b) : Nat) = n + a - b ↔ a < b := by
  cases' n with n
  · exact @finZeroElim (fun _ => _) a
  rw [lt_iff_val_lt_val, Fin.coe_sub, add_comm]
  cases' le_or_lt (b : Nat) a with h h
  · refine iff_of_false ?_ (not_lt_of_le h)
    simpa [add_tsub_assoc_of_le h] using
      ((Nat.mod_lt _ (Nat.succ_pos _)).trans_le le_self_add).ne
  · simp [← tsub_tsub_assoc b.is_lt.le h.le, ← tsub_add_eq_add_tsub b.is_lt.le,
      Nat.mod_eq_of_lt (tsub_lt_self (Nat.succ_pos _) (tsub_pos_of_lt h)), val_fin_le.mp _]
    exact h

@[simp]
theorem lt_sub_one_iff {n : Nat} {k : Fin (n + 2)} : k < k - 1 ↔ k = 0 := by
  rcases k with ⟨_ | k, hk⟩
  simp [lt_iff_val_lt_val]
  have : (k + 1 + (n + 1)) % (n + 2) = k % (n + 2) := by
    rw [add_right_comm, add_assoc, add_mod_right]
  simp [lt_iff_val_lt_val, ext_iff, Fin.coe_sub, succ_eq_add_one, this,
    mod_eq_of_lt ((lt_succ_self _).trans hk)]

@[simp]
theorem le_sub_one_iff {n : Nat} {k : Fin (n + 1)} : k ≤ k - 1 ↔ k = 0 := by
  cases n
  · simp [fin_one_eq_zero k]
  rw [← lt_sub_one_iff, le_iff_lt_or_eq, lt_sub_one_iff, or_iff_left_iff_imp, eq_comm,
    sub_eq_iff_eq_add]
  simp

@[simp]
theorem sub_one_lt_iff {n : Nat} {k : Fin (n + 1)} : k - 1 < k ↔ 0 < k :=
  not_iff_not.1 <| by simp only [not_lt, le_sub_one_iff, le_zero_iff]

theorem last_sub (i : Fin (n + 1)) : last n - i = Fin.rev i :=
  ext <| by rw [coe_sub_iff_le.2 i.le_last, val_last, val_rev, Nat.succ_sub_succ_eq_sub]

end AddGroup

section SuccAbove

theorem succAbove_aux (p : Fin (n + 1)) :
    StrictMono fun i : Fin n => if (castSucc i) < p then (castSucc i) else i.succ :=
  (castSucc : Fin n ↪o _).strictMono.ite (succEmbedding n).strictMono
    (fun _ _ hij hj => lt_trans ((castSucc : Fin n ↪o _).lt_iff_lt.2 hij) hj) fun i =>
    (castSucc_lt_succ i).le

/-- `succAbove p i` embeds `Fin n` into `Fin (n + 1)` with a hole around `p`. -/
def succAbove (p : Fin (n + 1)) : Fin n ↪o Fin (n + 1) :=
  OrderEmbedding.ofStrictMono _ p.succAbove_aux

/-- Embedding `i : Fin n` into `Fin (n + 1)` with a hole around `p : Fin (n + 1)`
embeds `i` by `castSucc` when the resulting `i.castSucc < p`. -/
theorem succAbove_below (p : Fin (n + 1)) (i : Fin n) (h : castSucc i < p) :
    p.succAbove i = castSucc i := if_pos h

@[simp]
theorem succAbove_ne_zero_zero [NeZero n] {a : Fin (n + 1)} (ha : a ≠ 0) : a.succAbove 0 = 0 := by
  rw [Fin.succAbove_below]
  · simp
  · simp only [castSucc_zero]
    exact bot_lt_iff_ne_bot.mpr ha

theorem succAbove_eq_zero_iff [NeZero n] {a : Fin (n + 1)} {b : Fin n} (ha : a ≠ 0) :
    a.succAbove b = 0 ↔ b = 0 := by
  simp only [← succAbove_ne_zero_zero ha, OrderEmbedding.eq_iff_eq, iff_self]

theorem succAbove_ne_zero [NeZero n] {a : Fin (n + 1)} {b : Fin n} (ha : a ≠ 0) (hb : b ≠ 0) :
    a.succAbove b ≠ 0 :=
  mt (succAbove_eq_zero_iff ha).mp hb

/-- Embedding `Fin n` into `Fin (n + 1)` with a hole around zero embeds by `succ`. -/
@[simp]
theorem succAbove_zero : ⇑(succAbove (0 : Fin (n + 1))) = Fin.succ :=
  rfl

/-- Embedding `Fin n` into `Fin (n + 1)` with a hole around `last n` embeds by `castSucc`. -/
@[simp]
theorem succAbove_last : succAbove (Fin.last n) = castSucc := by
  ext
  simp only [succAbove_below, castSucc_lt_last]

theorem succAbove_last_apply (i : Fin n) : succAbove (Fin.last n) i = castSucc i := by
  rw [succAbove_last]

/-- Embedding `i : Fin n` into `Fin (n + 1)` with a hole around `p : Fin (n + 1)`
embeds `i` by `succ` when the resulting `p < i.succ`. -/
theorem succAbove_above (p : Fin (n + 1)) (i : Fin n) (h : p ≤ castSucc i) :
    p.succAbove i = i.succ := by simp [succAbove, h.not_lt]

/-- Embedding `i : Fin n` into `Fin (n + 1)` is always about some hole `p`. -/
theorem succAbove_lt_ge (p : Fin (n + 1)) (i : Fin n) : castSucc i < p ∨ p ≤ castSucc i :=
  lt_or_ge (castSucc i) p

/-- Embedding `i : Fin n` into `Fin (n + 1)` is always about some hole `p`. -/
theorem succAbove_lt_gt (p : Fin (n + 1)) (i : Fin n) : castSucc i < p ∨ p < i.succ :=
  Or.casesOn (succAbove_lt_ge p i) (fun h => Or.inl h) fun h =>
    Or.inr (lt_of_le_of_lt h (castSucc_lt_succ i))

/-- Embedding `i : Fin n` into `Fin (n + 1)` using a pivot `p` that is greater
results in a value that is less than `p`. -/
@[simp]
theorem succAbove_lt_iff (p : Fin (n + 1)) (i : Fin n) : p.succAbove i < p ↔ castSucc i < p := by
  refine' Iff.intro _ _
  · intro h
    cases' succAbove_lt_ge p i with H H
    · exact H
    · rw [succAbove_above _ _ H] at h
      exact lt_trans (castSucc_lt_succ i) h
  · intro h
    rw [succAbove_below _ _ h]
    exact h

/-- Embedding `i : Fin n` into `Fin (n + 1)` using a pivot `p` that is lesser
results in a value that is greater than `p`. -/
theorem lt_succAbove_iff (p : Fin (n + 1)) (i : Fin n) : p < p.succAbove i ↔ p ≤ castSucc i := by
  refine' Iff.intro _ _
  · intro h
    cases' succAbove_lt_ge p i with H H
    · rw [succAbove_below _ _ H] at h
      exact le_of_lt h
    · exact H
  · intro h
    rw [succAbove_above _ _ h]
    exact lt_of_le_of_lt h (castSucc_lt_succ i)

/-- Embedding `i : Fin n` into `Fin (n + 1)` with a hole around `p : Fin (n + 1)`
never results in `p` itself -/
theorem succAbove_ne (p : Fin (n + 1)) (i : Fin n) : p.succAbove i ≠ p := by
  intro eq
  by_cases H : castSucc i < p
  · simp [lt_irrefl, ← succAbove_below _ _ H, eq] at H
  · simpa [← succAbove_above _ _ (le_of_not_lt H), eq, H] using castSucc_lt_succ i

/-- Embedding a positive `Fin n` results in a positive `Fin (n + 1)` -/
theorem succAbove_pos [NeZero n] (p : Fin (n + 1)) (i : Fin n) (h : 0 < i) : 0 < p.succAbove i := by
  by_cases H : castSucc i < p
  · simpa [succAbove_below _ _ H] using castSucc_pos h
  · simp [succAbove_above _ _ (le_of_not_lt H)]

@[simp]
theorem succAbove_castLT {x y : Fin (n + 1)} (h : x < y)
    (hx : x.1 < n := lt_of_lt_of_le h y.le_last) : y.succAbove (x.castLT hx) = x := by
  rw [succAbove_below, castSucc_castLT]
  exact h

@[simp]
theorem succAbove_pred {x y : Fin (n + 1)} (h : x < y) (hy : y ≠ 0 := (x.zero_le.trans_lt h).ne') :
    x.succAbove (y.pred hy) = y := by
  rw [succAbove_above, succ_pred]
  simpa [le_iff_val_le_val] using Nat.le_pred_of_lt h

theorem castLT_succAbove {x : Fin n} {y : Fin (n + 1)} (h : castSucc x < y)
    (h' : (y.succAbove x).1 < n := lt_of_lt_of_le ((succAbove_lt_iff _ _).2 h) (le_last y)) :
    (y.succAbove x).castLT h' = x := by simp only [succAbove_below _ _ h, castLT_castSucc]

theorem pred_succAbove {x : Fin n} {y : Fin (n + 1)} (h : y ≤ castSucc x)
    (h' : y.succAbove x ≠ 0 := (y.zero_le.trans_lt <| (lt_succAbove_iff _ _).2 h).ne') :
    (y.succAbove x).pred h' = x := by simp only [succAbove_above _ _ h, pred_succ]

theorem exists_succAbove_eq {x y : Fin (n + 1)} (h : x ≠ y) : ∃ z, y.succAbove z = x := by
  cases' h.lt_or_lt with hlt hlt
  exacts [⟨_, succAbove_castLT hlt⟩, ⟨_, succAbove_pred hlt⟩]

@[simp]
theorem exists_succAbove_eq_iff {x y : Fin (n + 1)} : (∃ z, x.succAbove z = y) ↔ y ≠ x := by
  refine' ⟨_, exists_succAbove_eq⟩
  rintro ⟨y, rfl⟩
  exact succAbove_ne _ _

/-- The range of `p.succAbove` is everything except `p`. -/
@[simp]
theorem range_succAbove (p : Fin (n + 1)) : Set.range p.succAbove = {p}ᶜ :=
  Set.ext fun _ => exists_succAbove_eq_iff

@[simp]
theorem range_succ (n : Nat) : Set.range (Fin.succ : Fin n → Fin (n + 1)) = {0}ᶜ := by
  rw [← succAbove_zero]
  exact range_succAbove (0 : Fin (n + 1))

@[simp]
theorem exists_succ_eq_iff {x : Fin (n + 1)} : (∃ y, Fin.succ y = x) ↔ x ≠ 0 := by
  convert @exists_succAbove_eq_iff n 0 x

/-- Given a fixed pivot `x : Fin (n + 1)`, `x.succAbove` is injective -/
theorem succAbove_right_injective {x : Fin (n + 1)} : Injective (succAbove x) :=
  (succAbove x).injective

/-- Given a fixed pivot `x : Fin (n + 1)`, `x.succAbove` is injective -/
theorem succAbove_right_inj {x : Fin (n + 1)} : x.succAbove a = x.succAbove b ↔ a = b :=
  succAbove_right_injective.eq_iff

/-- `succAbove` is injective at the pivot -/
theorem succAbove_left_injective : Injective (@succAbove n) := fun _ _ h => by
  simpa [range_succAbove] using congr_arg (fun f : Fin n ↪o Fin (n + 1) => Set.range fᶜ) h

/-- `succAbove` is injective at the pivot -/
@[simp]
theorem succAbove_left_inj {x y : Fin (n + 1)} : x.succAbove = y.succAbove ↔ x = y :=
  succAbove_left_injective.eq_iff

@[simp]
theorem zero_succAbove {n : Nat} (i : Fin n) : (0 : Fin (n + 1)).succAbove i = i.succ := by
  rfl

@[simp]
theorem succ_succAbove_zero {n : Nat} [NeZero n] (i : Fin n) : succAbove i.succ 0 = 0 :=
  succAbove_below i.succ 0 (by simp only [castSucc_zero, succ_pos])

@[simp]
theorem succ_succAbove_succ {n : Nat} (i : Fin (n + 1)) (j : Fin n) :
    i.succ.succAbove j.succ = (i.succAbove j).succ :=
  (lt_or_ge (castSucc j) i).elim
    (fun h => by
      have h' : castSucc j.succ < i.succ := by simpa [lt_iff_val_lt_val] using h
      ext
      simp [succAbove_below _ _ h, succAbove_below _ _ h'])
    fun h => by
    have h' : i.succ ≤ castSucc j.succ := by simpa [le_iff_val_le_val] using h
    ext
    simp [succAbove_above _ _ h, succAbove_above _ _ h']

--@[simp] -- porting note: can be proved by `simp`
theorem one_succAbove_zero {n : Nat} : (1 : Fin (n + 2)).succAbove 0 = 0 := by
  rfl

/-- By moving `succ` to the outside of this expression, we create opportunities for further
simplification using `succAbove_zero` or `succ_succAbove_zero`. -/
@[simp]
theorem succ_succAbove_one {n : Nat} [NeZero n] (i : Fin (n + 1)) :
    i.succ.succAbove 1 = (i.succAbove 0).succ := by
  rw [← succ_zero_eq_one]
  exact succ_succAbove_succ i 0

@[simp]
theorem one_succAbove_succ {n : Nat} (j : Fin n) :
    (1 : Fin (n + 2)).succAbove j.succ = j.succ.succ := by
  have := succ_succAbove_succ 0 j
  rwa [succ_zero_eq_one, zero_succAbove] at this

@[simp]
theorem one_succAbove_one {n : Nat} : (1 : Fin (n + 3)).succAbove 1 = 2 := by
  have := succ_succAbove_succ (0 : Fin (n + 2)) (0 : Fin (n + 2))
  simp only [succ_zero_eq_one, val_zero, Nat.cast_zero, zero_succAbove, succ_one_eq_two] at this
  exact this

end SuccAbove

section PredAbove

/-- `predAbove p i` embeds `i : Fin (n+1)` into `Fin n` by subtracting one if `p < i`. -/
def predAbove (p : Fin n) (i : Fin (n + 1)) : Fin n :=
  if h : castSucc p < i then i.pred (_root_.ne_of_lt (lt_of_le_of_lt (zero_le (castSucc p)) h)).symm
  else i.castLT (lt_of_le_of_lt (le_of_not_lt h) p.2)

theorem predAbove_right_monotone (p : Fin n) : Monotone p.predAbove := fun a b H => by
  dsimp [predAbove]
  split_ifs with ha hb hb
  all_goals simp only [le_iff_val_le_val, coe_pred]
  · exact pred_le_pred H
  · calc
      _ ≤ _ := Nat.pred_le _
      _ ≤ _ := H
  · simp at ha
    exact le_pred_of_lt (lt_of_le_of_lt ha hb)
  · exact H

theorem predAbove_left_monotone (i : Fin (n + 1)) :
    Monotone fun p => predAbove p i := fun a b H => by
  dsimp [predAbove]
  split_ifs with ha hb hb
  · rfl
  · exact pred_le _
  · have : b < a := castSucc_lt_castSucc_iff.mpr (hb.trans_le (le_of_not_gt ha))
    exact absurd H this.not_le
  · rfl

/-- `castPred` embeds `i : Fin (n + 2)` into `Fin (n + 1)`
by lowering just `last (n + 1)` to `last n`. -/
def castPred (i : Fin (n + 2)) : Fin (n + 1) :=
  predAbove (last n) i

@[simp]
theorem castPred_zero : castPred (0 : Fin (n + 2)) = 0 :=
  rfl

@[simp]
theorem castPred_one : castPred (1 : Fin (n + 2)) = 1 := by
  cases n
  · rfl
  · rfl

@[simp]
theorem predAbove_zero {i : Fin (n + 2)} (hi : i ≠ 0) : predAbove 0 i = i.pred hi := by
  dsimp [predAbove]
  rw [dif_pos]
  simp only [castSucc_zero]
  exact (pos_iff_ne_zero _).mpr hi

@[simp]
theorem castPred_last : castPred (last (n + 1)) = last n :=
  eq_of_veq (by simp [castPred, predAbove, castSucc_lt_last])

--Porting note: removing @[simp]. `castPred_mk'` has `simp` attribute instead
theorem castPred_mk (n i : Nat) (h : i < n + 1) : castPred ⟨i, lt_succ_of_lt h⟩ = ⟨i, h⟩ := by
  have : ¬castSucc (last n) < ⟨i, lt_succ_of_lt h⟩ := by
    simpa [lt_iff_val_lt_val] using le_of_lt_succ h
  simp [castPred, predAbove, this]

--Porting note: new theorem
@[simp]
theorem castPred_mk' (n i : Nat) (h₁ : i < n + 2) (h₂ : i < n + 1) : castPred ⟨i, h₁⟩ = ⟨i, h₂⟩ :=
  castPred_mk _ _ _

theorem coe_castPred {n : Nat} (a : Fin (n + 2)) (hx : a < Fin.last _) :
  (a.castPred : Nat) = a := by
  rcases a with ⟨a, ha⟩
  rw [castPred_mk]
  exact hx

theorem predAbove_below (p : Fin (n + 1)) (i : Fin (n + 2)) (h : i ≤ castSucc p) :
    p.predAbove i = i.castPred := by
  have : i ≤ castSucc (last n) := h.trans p.le_last
  simp [predAbove, castPred, h.not_lt, this.not_lt]

@[simp]
theorem predAbove_last : predAbove (Fin.last n) = castPred :=
  rfl

theorem predAbove_last_apply (i : Fin n) : predAbove (Fin.last n) i = i.castPred := by
  rw [predAbove_last]

theorem predAbove_above (p : Fin n) (i : Fin (n + 1)) (h : castSucc p < i) :
    p.predAbove i = i.pred ((castSucc p).zero_le.trans_lt h).ne.symm := by simp [predAbove, h]

theorem castPred_monotone : Monotone (@castPred n) :=
  predAbove_right_monotone (last _)

/-- Sending `Fin (n+1)` to `Fin n` by subtracting one from anything above `p`
then back to `Fin (n+1)` with a gap around `p` is the identity away from `p`. -/
@[simp]
theorem succAbove_predAbove {p : Fin n} {i : Fin (n + 1)} (h : i ≠ castSucc p) :
    p.castSucc.succAbove (p.predAbove i) = i := by
  dsimp [predAbove, succAbove]
  rcases p with ⟨p, _⟩
  rcases i with ⟨i, _⟩
  cases' lt_or_le i p with H H
  · rw [dif_neg]
    rw [if_pos]
    rfl
    exact H
    simp
    apply le_of_lt H
  · rw [dif_pos]
    rw [if_neg]
    · simp
    · simp only [pred, Fin.mk_lt_mk, not_lt]
      exact Nat.le_pred_of_lt (h.symm.lt_of_le H)
    · exact lt_of_le_of_ne H h.symm

/-- Sending `Fin n` into `Fin (n + 1)` with a gap at `p`
then back to `Fin n` by subtracting one from anything above `p` is the identity. -/
@[simp]
theorem predAbove_succAbove (p : Fin n) (i : Fin n) :
    p.predAbove ((castSucc p).succAbove i) = i := by
  dsimp [predAbove, succAbove]
  rcases p with ⟨p, _⟩
  rcases i with ⟨i, _⟩
  dsimp
  split_ifs with h₁ h₂ h₃
  · simp only [← val_fin_lt, not_lt] at h₁ h₂
    exact (lt_le_antisymm h₁ (le_of_lt h₂)).elim
  · rfl
  · rfl
  · simp only [← val_fin_lt, not_lt] at h₁ h₃
    contradiction

theorem castSucc_pred_eq_pred_castSucc {a : Fin (n + 1)} (ha : a ≠ 0)
    (ha' := a.castSucc_ne_zero_iff.mpr ha) : castSucc (a.pred ha) = (castSucc a).pred ha' := by
  cases a
  rfl

/-- `pred` commutes with `succAbove`. -/
theorem pred_succAbove_pred {a : Fin (n + 2)} {b : Fin (n + 1)} (ha : a ≠ 0) (hb : b ≠ 0)
    (hk := succAbove_ne_zero ha hb) :
    (a.pred ha).succAbove (b.pred hb) = (a.succAbove b).pred hk := by
  obtain hbelow | habove := lt_or_le (castSucc b) a
  -- `rwa` uses them
  · rw [Fin.succAbove_below]
    · rwa [castSucc_pred_eq_pred_castSucc, Fin.pred_inj, Fin.succAbove_below]
    · rwa [castSucc_pred_eq_pred_castSucc, pred_lt_pred_iff]
  · rw [Fin.succAbove_above]
    have : (b.pred hb).succ = b.succ.pred (Fin.succ_ne_zero _) := by rw [succ_pred, pred_succ]
    · rwa [this, Fin.pred_inj, Fin.succAbove_above]
    · rwa [castSucc_pred_eq_pred_castSucc, Fin.pred_le_pred_iff]

/-- `succ` commutes with `predAbove`. -/
@[simp]
theorem succ_predAbove_succ {n : Nat} (a : Fin n) (b : Fin (n + 1)) :
    a.succ.predAbove b.succ = (a.predAbove b).succ := by
  obtain h₁ | h₂ := lt_or_le (castSucc a) b
  · rw [Fin.predAbove_above _ _ h₁, Fin.succ_pred, Fin.predAbove_above, Fin.pred_succ]
    simpa only [lt_iff_val_lt_val, coe_castSucc, val_succ, add_lt_add_iff_right] using
      h₁
  · cases' n with n
    · exfalso
      exact not_lt_zero' a.is_lt
    · rw [Fin.predAbove_below a b h₂,
        Fin.predAbove_below a.succ b.succ
          (by
            simpa only [le_iff_val_le_val, val_succ, coe_castSucc, add_le_add_iff_right] using h₂)]
      ext
      have h₀ : (b : Nat) < n + 1 := by
        simp only [le_iff_val_le_val, coe_castSucc] at h₂
        simpa only [lt_succ_iff] using h₂.trans a.is_le
      have h₁ : (b.succ : Nat) < n + 2 := by
        rw [← Nat.succ_lt_succ_iff] at h₀
        simpa only [val_succ] using h₀
      simp only [coe_castPred b h₀, coe_castPred b.succ h₁, val_succ]

@[simp]
theorem castPred_castSucc (i : Fin (n + 1)) : castPred (castSucc i) = i := by
  simp [castPred, predAbove, not_lt.mpr (le_last i)]

theorem castSucc_castPred {i : Fin (n + 2)} (h : i < last (n + 1)) : castSucc i.castPred = i := by
  rw [castPred, predAbove, dif_neg]
  · simp [Fin.eq_iff_veq]
  · exact h.not_le

theorem coe_castPred_le_self (i : Fin (n + 2)) : (i.castPred : Nat) ≤ i := by
  rcases i.le_last.eq_or_lt with (rfl | h)
  · simp
  · rw [castPred, predAbove, dif_neg]
    · simp
    · simpa [lt_iff_val_lt_val, le_iff_val_le_val, lt_succ_iff] using h

theorem coe_castPred_lt_iff {i : Fin (n + 2)} : (i.castPred : Nat) < i ↔ i = Fin.last _ := by
  rcases i.le_last.eq_or_lt with (rfl | H)
  · simp
  · simp only [_root_.ne_of_lt H]
    rw [← castSucc_castPred H]
    simp

theorem lt_last_iff_coe_castPred {i : Fin (n + 2)} :
    i < Fin.last _ ↔ (i.castPred : Nat) = i := by
  rcases i.le_last.eq_or_lt with (rfl | H)
  · simp
  · simp only [H]
    rw [← castSucc_castPred H]
    simp

end PredAbove

/-- `min n m` as an element of `Fin (m + 1)` -/
def clamp (n m : Nat) : Fin (m + 1) :=
  Nat.cast <| min n m

@[simp]
theorem coe_clamp (n m : Nat) : (clamp n m : Nat) = min n m :=
  Nat.mod_eq_of_lt <| Nat.lt_succ_iff.mpr <| min_le_right _ _

@[simp]
theorem coe_ofNat_eq_mod (m n : Nat) [NeZero m] :
    ((n : Fin m) : Nat) = n % m :=
  rfl

section Mul

/-!
### mul
-/

theorem val_mul {n : Nat} : ∀ a b : Fin n, (a * b).val = a.val * b.val % n
  | ⟨_, _⟩, ⟨_, _⟩ => rfl

theorem coe_mul {n : Nat} : ∀ a b : Fin n, ((a * b : Fin n) : Nat) = a * b % n
  | ⟨_, _⟩, ⟨_, _⟩ => rfl

protected theorem mul_one [NeZero n] (k : Fin n) : k * 1 = k := by
  cases' n with n
  · simp
  cases n
  · simp [fin_one_eq_zero]
  simp [eq_iff_veq, mul_def, mod_eq_of_lt (is_lt k)]

protected theorem mul_comm (a b : Fin n) : a * b = b * a :=
  Fin.eq_of_veq <| by rw [mul_def, mul_def, mul_comm]


protected theorem one_mul [NeZero n] (k : Fin n) : (1 : Fin n) * k = k := by
  rw [Fin.mul_comm, Fin.mul_one]

protected theorem mul_zero [NeZero n] (k : Fin n) : k * 0 = 0 := by simp [eq_iff_veq, mul_def]

protected theorem zero_mul [NeZero n] (k : Fin n) : (0 : Fin n) * k = 0 := by
  simp [eq_iff_veq, mul_def]

end Mul

open Qq in
instance toExpr (n : Nat) : Lean.ToExpr (Fin n) where
  toTypeExpr := q(Fin $n)
  toExpr := match n with
    | 0 => finZeroElim
    | k + 1 => fun i => show Q(Fin $n) from
      have i : Q(Nat) := Lean.mkNatLit i -- raw literal to avoid ofNat-double-wrapping
      have : Q(NeZero $n) := haveI : $n =Q $k + 1 := ⟨⟩; by exact q(NeZero.succ)
      q(OfNat.ofNat $i)

end Fin

namespace USize

@[simp] theorem lt_def {a b : USize} : a < b ↔ a.toNat < b.toNat := .rfl

@[simp] theorem le_def {a b : USize} : a ≤ b ↔ a.toNat ≤ b.toNat := .rfl

@[simp] theorem zero_toNat : (0 : USize).toNat = 0 := Nat.zero_mod _

@[simp] theorem mod_toNat (a b : USize) : (a % b).toNat = a.toNat % b.toNat :=
  Fin.mod_val ..

@[simp] theorem div_toNat (a b : USize) : (a / b).toNat = a.toNat / b.toNat :=
  Fin.div_val ..

@[simp] theorem modn_toNat (a : USize) (b : Nat) : (a.modn b).toNat = a.toNat % b :=
  Fin.modn_val ..

theorem mod_lt (a b : USize) (h : 0 < b) : a % b < b := USize.modn_lt _ (by simp at h; exact h)

theorem toNat.inj : ∀ {a b : USize}, a.toNat = b.toNat → a = b
  | ⟨_, _⟩, ⟨_, _⟩, rfl => rfl

end USize
