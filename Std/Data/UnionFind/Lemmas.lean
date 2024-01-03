/-
Copyright (c) 2021 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Std.Data.UnionFind.Basic

namespace Std.UnionFind

@[simp] theorem arr_empty : empty.arr = #[] := rfl
@[simp] theorem parent_empty : empty.parent a = a := rfl
@[simp] theorem rank_empty : empty.rank a = 0 := rfl
@[simp] theorem root_empty : empty.root a = a := rfl

@[simp] theorem arr_push {m : UnionFind} : m.push.arr = m.arr.push ⟨m.arr.size, 0⟩ := rfl

@[simp] theorem parentD_push {arr : Array UFNode} :
    parentD (arr.push ⟨arr.size, 0⟩) a = parentD arr a := by
  simp [parentD]; split <;> split <;> try simp [Array.get_push, *]
  · next h1 h2 =>
    simp [Nat.lt_succ] at h1 h2
    exact Nat.le_antisymm h2 h1
  · next h1 h2 => cases h1 (Nat.lt_succ_of_lt h2)

@[simp] theorem parent_push {m : UnionFind} : m.push.parent a = m.parent a := by simp [parent]

@[simp] theorem rankD_push {arr : Array UFNode} :
    rankD (arr.push ⟨arr.size, 0⟩) a = rankD arr a := by
  simp [rankD]; split <;> split <;> try simp [Array.get_push, *]
  next h1 h2 => cases h1 (Nat.lt_succ_of_lt h2)

@[simp] theorem rank_push {m : UnionFind} : m.push.rank a = m.rank a := by simp [rank]

@[simp] theorem rankMax_push {m : UnionFind} : m.push.rankMax = m.rankMax := by simp [rankMax]

@[simp] theorem root_push {self : UnionFind} : self.push.root x = self.root x :=
  root_ext fun _ => parent_push

@[simp] theorem arr_link : (link self x y yroot).arr = linkAux self.arr x y := rfl

theorem parentD_linkAux {self} {x y : Fin self.size} :
    parentD (linkAux self x y) i =
    if x.1 = y then
      parentD self i
    else
      if (self.get y).rank < (self.get x).rank then
        if y = i then x else parentD self i
      else
        if x = i then y else parentD self i := by
  dsimp only [linkAux]; split <;> [rfl; split] <;> [rw [parentD_set]; split] <;> rw [parentD_set]
  split <;> [(subst i; rwa [if_neg, parentD_eq]); rw [parentD_set]]

theorem parent_link {self} {x y : Fin self.size} (yroot) {i} :
    (link self x y yroot).parent i =
    if x.1 = y then
      self.parent i
    else
      if self.rank y < self.rank x then
        if y = i then x else self.parent i
      else
        if x = i then y else self.parent i := by
  simp [rankD_eq]; exact parentD_linkAux

theorem root_link {self : UnionFind} {x y : Fin self.size}
    (xroot : self.parent x = x) (yroot : self.parent y = y) :
    ∃ r, (r = x ∨ r = y) ∧ ∀ i,
      (link self x y yroot).root i =
      if self.root i = x ∨ self.root i = y then r.1 else self.root i := by
  if h : x.1 = y then
    refine ⟨x, .inl rfl, fun i => ?_⟩
    rw [root_ext (m2 := self) (fun _ => by rw [parent_link, if_pos h])]
    split <;> [obtain _ | _ := ‹_› <;> simp [*]; rfl]
  else
  have {x y : Fin self.size}
      (xroot : self.parent x = x) (yroot : self.parent y = y) {m : UnionFind}
      (hm : ∀ i, m.parent i = if y = i then x.1 else self.parent i) :
      ∃ r, (r = x ∨ r = y) ∧ ∀ i,
        m.root i = if self.root i = x ∨ self.root i = y then r.1 else self.root i := by
    let rec go (i) : m.root i = if self.root i = x ∨ self.root i = y then x.1 else self.root i := by
      if h : m.parent i = i then
        rw [root_eq_self.2 h]; rw [hm i] at h; split at h
        · rw [if_pos, h]; simp [← h, root_eq_self, xroot]
        · rw [root_eq_self.2 ‹_›]; split <;> [skip; rfl]
          next h' => exact h'.resolve_right (Ne.symm ‹_›)
      else
        have _ := Nat.sub_lt_sub_left (m.lt_rankMax i) (m.rank_lt h)
        rw [← root_parent, go (m.parent i)]
        rw [hm i]; split <;> [subst i; rw [root_parent]]
        simp [root_eq_self.2 xroot, root_eq_self.2 yroot]
    exact ⟨x, .inl rfl, go⟩
  if hr : self.rank y < self.rank x then
    exact this xroot yroot fun i => by simp [parent_link, h, hr]
  else
    simpa (config := {singlePass := true}) [or_comm] using
      this yroot xroot fun i => by simp [parent_link, h, hr]
termination_by go => m.rankMax - m.rank i

nonrec theorem Equiv.rfl : Equiv self a a := rfl
theorem Equiv.symm : Equiv self a b → Equiv self b a := .symm
theorem Equiv.trans : Equiv self a b → Equiv self b c → Equiv self a c := .trans

@[simp] theorem equiv_empty : Equiv empty a b ↔ a = b := by simp [Equiv]

@[simp] theorem equiv_push : Equiv self.push a b ↔ Equiv self a b := by simp [Equiv]

@[simp] theorem equiv_root : Equiv self (self.root a) a := by simp [Equiv, root_root]
@[simp] theorem equiv_root_l : Equiv self (self.root a) b ↔ Equiv self a b := by
  simp [Equiv, root_root]
@[simp] theorem equiv_root_r : Equiv self a (self.root b) ↔ Equiv self a b := by
  simp [Equiv, root_root]

theorem equiv_find : Equiv (self.find x).1 a b ↔ Equiv self a b := by simp [Equiv, find_root_1]

theorem equiv_link {self : UnionFind} {x y : Fin self.size}
    (xroot : self.parent x = x) (yroot : self.parent y = y) :
    Equiv (link self x y yroot) a b ↔
    Equiv self a b ∨ Equiv self a x ∧ Equiv self y b ∨ Equiv self a y ∧ Equiv self x b := by
  have {m : UnionFind} {x y : Fin self.size}
      (xroot : self.root x = x) (yroot : self.root y = y)
      (hm : ∀ i, m.root i = if self.root i = x ∨ self.root i = y then x.1 else self.root i) :
      Equiv m a b ↔
      Equiv self a b ∨ Equiv self a x ∧ Equiv self y b ∨ Equiv self a y ∧ Equiv self x b := by
    simp [Equiv, hm, xroot, yroot]
    by_cases h1 : root self a = x <;> by_cases h2 : root self b = x <;>
      simp [h1, h2, imp_false, Decidable.not_not]
    · simp [h2, Ne.symm h2]; split <;> simp [@eq_comm _ _ (root self b), *]
    · by_cases h1 : root self a = y <;> by_cases h2 : root self b = y <;>
        simp [h1, h2, @eq_comm _ _ (root self b), *]
  obtain ⟨r, ha, hr⟩ := root_link xroot yroot; revert hr
  rw [← root_eq_self] at xroot yroot
  obtain rfl | rfl := ha
  · exact this xroot yroot
  · simpa [or_comm, and_comm] using this yroot xroot

theorem equiv_union {self : UnionFind} {x y : Fin self.size} :
    Equiv (union self x y) a b ↔
    Equiv self a b ∨ Equiv self a x ∧ Equiv self y b ∨ Equiv self a y ∧ Equiv self x b := by
  simp [union]; rw [equiv_link (by simp [← root_eq_self, root_root])]; simp [equiv_find]
