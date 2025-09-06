/-
Copyright (c) 2024 Shreyas Srinivas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shreyas Srinivas, François G. Dorais, Eric Wieser
-/


namespace Vector

theorem toArray_injective : ∀ {v w : Vector α n}, v.toArray = w.toArray → v = w
  | {..}, {..}, rfl => rfl


/-! ### mk lemmas -/

@[simp] theorem get_mk (a : Array α) (h : a.size = n) (i) :
    (Vector.mk a h).get i = a[i] := rfl

@[simp] theorem getD_mk (a : Array α) (h : a.size = n) (i x) :
    (Vector.mk a h).getD i x = a.getD i x := rfl

@[simp] theorem uget_mk (a : Array α) (h : a.size = n) (i) (hi : i.toNat < n) :
    (Vector.mk a h).uget i hi = a.uget i (by simp [h, hi]) := rfl

/-! ### tail lemmas -/

theorem tail_eq_of_zero {v : Vector α 0} : v.tail = #v[] := Vector.eq_empty

theorem tail_eq_of_ne_zero [NeZero n] {v : Vector α n} :
    v.tail = v.eraseIdx 0 n.pos_of_neZero := by
  simp only [tail_eq_cast_extract]
  ext
  simp only [getElem_cast, getElem_extract, getElem_eraseIdx, Nat.not_lt_zero, ↓reduceDIte]
  congr 1
  omega

-- This is not a `@[simp]` lemma because the LHS simplifies to `Vector.extract`.
theorem toList_tail {v : Vector α n} :
    v.tail.toList = v.toList.tail :=
  match n with
  | 0 => by simp [Vector.eq_empty]
  | _ + 1 => by
    apply List.ext_getElem
    · simp
    · intro i h₁ h₂
      simp only [Nat.add_one_sub_one, tail_eq_cast_extract, getElem_toList, getElem_cast,
        getElem_extract, List.getElem_tail]
      congr 1
      omega

/-! ### getElem lemmas -/

theorem getElem_tail {v : Vector α n} {i : Nat} (hi : i < n - 1) :
    v.tail[i] = v[i + 1] :=
  match n with
  | _ + 1 =>
    getElem_congr_coll tail_eq_of_ne_zero |>.trans <|
    getElem_eraseIdx (Nat.zero_lt_succ _) hi

/-! ### get lemmas -/

theorem get_eq_getElem (v : Vector α n) (i : Fin n) : v.get i = v[(i : Nat)] := rfl

@[simp] theorem get_push_last (v : Vector α n) (a : α) :
    (v.push a).get (Fin.last n) = a :=
  getElem_push_last

@[simp] theorem get_push_castSucc (v : Vector α n) (a : α) (i : Fin n) :
    (v.push a).get (Fin.castSucc i) = v.get i :=
  getElem_push_lt _

@[simp] theorem get_map (v : Vector α n) (f : α → β) (i : Fin n) :
    (v.map f).get i = f (v.get i) :=
  getElem_map _ _

@[simp] theorem get_reverse (v : Vector α n) (i : Fin n) :
    v.reverse.get i = v.get (i.rev) :=
  getElem_reverse _ |>.trans <| congrArg v.get <| Fin.ext <| by simp; omega

@[simp] theorem get_replicate (n : Nat) (a : α) (i : Fin n) : (replicate n a).get i = a :=
  getElem_replicate _

@[simp] theorem get_range (n : Nat) (i : Fin n) : (range n).get i = i :=
  getElem_range _

@[simp] theorem get_ofFn (f : Fin n → α) (i : Fin n) : (ofFn f).get i = f i :=
  getElem_ofFn _

@[simp] theorem get_cast (v : Vector α m) (h : m = n) (i : Fin n) :
    (v.cast h).get i = v.get (i.cast h.symm) :=
  getElem_cast _

-- This is not a `@[simp]` lemma because the LHS simplifies to `Vector.extract`.
theorem get_tail (v : Vector α (n + 1)) (i : Fin n) :
    v.tail.get i = v.get i.succ := getElem_tail _

/-! ### finIdxOf? lemmas -/

@[simp]
theorem finIdxOf?_empty [BEq α] (v : Vector α 0) : v.finIdxOf? a = none := by
  simp [v.eq_empty]

@[simp]
theorem finIdxOf?_eq_none_iff [BEq α] [LawfulBEq α] {v : Vector α n} {a : α} :
    v.finIdxOf? a = none ↔ a ∉ v := by
  obtain ⟨xs, rfl⟩ := v
  simp

@[simp]
theorem finIdxOf?_eq_some_iff [BEq α] [LawfulBEq α] {v : Vector α n} {a : α} {i : Fin n} :
    v.finIdxOf? a = some i ↔ v.get i = a ∧ ∀ j < i, ¬v.get j = a := by
  obtain ⟨xs, rfl⟩ := v
  simp

@[simp]
theorem isSome_finIdxOf? [BEq α] [PartialEquivBEq α] {v : Vector α n} {a : α} :
    (v.finIdxOf? a).isSome = v.contains a := by
  obtain ⟨v, rfl⟩ := v
  simp

@[simp]
theorem isNone_finIdxOf? [BEq α] [PartialEquivBEq α] {v : Vector α n} {a : α} :
    (v.finIdxOf? a).isNone = !v.contains a := by
  obtain ⟨v, rfl⟩ := v
  simp
