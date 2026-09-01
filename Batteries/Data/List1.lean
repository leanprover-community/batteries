/-
Copyright (c) 2026 Robin Arnez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robin Arnez
-/
module

@[expose] public section

/-- Nonempty list type. -/
@[ext, grind ext]
structure List1 (α : Type u) where
  /-- The underlying list -/
  toList : List α
  /-- The underlying list is not empty -/
  toList_ne_nil : toList ≠ []
deriving DecidableEq, Hashable

attribute [coe] List1.toList
instance : CoeOut (List1 α) (List α) := ⟨List1.toList⟩

instance [Inhabited α] : Inhabited (List1 α) := ⟨[default], nofun⟩
instance [BEq α] : BEq (List1 α) := ⟨fun a b => a.toList == b.toList⟩
instance [BEq α] [ReflBEq α] : ReflBEq (List1 α) := ⟨BEq.rfl (α := List α)⟩
instance [BEq α] [LawfulBEq α] : LawfulBEq (List1 α) where
  eq_of_beq h := List1.ext (eq_of_beq h)

attribute [simp, grind .] List1.toList_ne_nil

/-- `head :: tail` as a `List1 α`. -/
@[match_pattern, inline]
def List1.cons (head : α) (tail : List α) : List1 α :=
  ⟨head :: tail, nofun⟩

/-- The first element of the list -/
@[inline]
def List1.head (self : List1 α) : α :=
  self.toList.head self.toList_ne_nil

/-- All elements of the list except the first -/
@[inline]
def List1.tail (self : List1 α) : List α :=
  self.toList.tail

/-- The length of the list -/
@[inline]
def List1.length (l : List1 α) : Nat := l.toList.length

instance : Append (List1 α) where
  append a b := ⟨a ++ b, by simp⟩

-- Those don't work because the coercion exists
/-
instance : HAppend (List1 α) (List α) (List1 α) where
  hAppend a b := ⟨a ++ b, by simp⟩
instance : HAppend (List α) (List1 α) (List1 α) where
  hAppend a b := ⟨a ++ b, by simp⟩
-/

instance : GetElem (List1 α) Nat α (fun l i => i < l.length) where
  getElem l i h := l.toList[i]

@[grind =] theorem List1.cons_def (h : α) (t : List α) : cons h t = ⟨h :: t, nofun⟩ := rfl
@[simp] theorem List1.toList_cons (h : α) (t : List α) :
    (cons h t).toList = h :: t := rfl
theorem List1.toList_mk {l : List α} (h : l ≠ []) :
    (mk l h : List α) = l := rfl
theorem List1.mk_toList (l : List1 α) : mk l.toList l.toList_ne_nil = l := rfl

@[grind =] theorem List1.head_def (l : List1 α) : l.head = l.toList.head l.toList_ne_nil := rfl
@[simp] theorem List1.head_cons (h : α) (t : List α) : (cons h t).head = h := rfl
@[simp] theorem List1.head_mk {l : List α} (h : l ≠ []) : (mk l h).head = l.head h := rfl

@[grind =] theorem List1.tail_def (l : List1 α) : l.tail = l.toList.tail := rfl
@[simp] theorem List1.tail_cons (h : α) (t : List α) : (cons h t).tail = t := rfl
@[simp] theorem List1.tail_mk {l : List α} (h : l ≠ []) : (mk l h).tail = l.tail := rfl

@[simp] theorem List1.cons_head_tail : (l : List1 α) → cons l.head l.tail = l
  | cons h t => rfl

@[grind =] theorem List1.length_def (l : List1 α) : l.length = l.toList.length := rfl
@[simp] theorem List1.length_cons (h : α) (t : List α) : (cons h t).length = t.length + 1 := rfl
@[simp] theorem List1.length_mk {l : List α} (h : l ≠ []) : (mk l h).length = l.length := rfl

@[simp, grind .] theorem List1.length_ne_zero : (l : List1 α) → l.length ≠ 0
  | cons _ _ => nofun
@[simp] theorem List1.zero_ne_length : (l : List1 α) → 0 ≠ l.length
  | cons _ _ => nofun
@[simp] theorem List1.length_pos (l : List1 α) : 0 < l.length :=
  Nat.pos_of_ne_zero l.length_ne_zero

@[grind =] theorem List1.append_def (l l' : List1 α) : l ++ l' = ⟨l ++ l', by simp⟩ := rfl
@[simp, grind =] theorem List1.getElem_def {l : List1 α} {i : Nat} (h : i < l.length) :
    l[i] = l.toList[i] := rfl
