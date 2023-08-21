/-
Copyright (c) 2023 F. G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: F. G. Dorais
-/
import Std.Data.Array.Basic
import Std.Data.Array.Lemmas

namespace Array

/-- Prefix table for the Knuth-Morris-Pratt matching algorithm

  This is an array of the form `t = [(x₀,n₀), (x₁,n₁), (x₂, n₂), ...]` where for each `i`, `nᵢ` is
  the length of the longest proper prefix of `xs = [x₀,x₁,...,xᵢ]` which is also a suffix of `xs`.
-/
structure PrefixTable (α : Type _) extends Array (α × Nat) where
  /-- Validity condition to help with termination proofs -/
  valid : (h : i < toArray.size) → toArray[i].2 ≤ i

instance : Inhabited (PrefixTable α) where
  default := ⟨#[], fun .⟩

/-- Returns the size of the prefix table -/
abbrev PrefixTable.size (t : PrefixTable α) := t.toArray.size

/-- Returns the pattern array of the prefix table -/
abbrev PrefixTable.pattern (t : PrefixTable α) : Array α := t.toArray.map Prod.fst

/-- Transition function for the KMP matcher

  Assuming we have an input `xs` with a suffix that matches the pattern prefix `t.pattern[:len]`
  where `len : Fin (t.size+1)`. Then `xs.push x` has a suffix that matches the pattern prefix
  `t.pattern[:t.step x len]`. If `len` is as large as possible then `t.step x len` will also be
  as large as possible.
-/
def PrefixTable.step [BEq α] (t : PrefixTable α) (x : α) : Fin (t.size+1) → Fin (t.size+1)
| ⟨k, hk⟩ =>
  if hx : some x == t.pattern[k]? then
    have : k < t.size := by
      apply Nat.lt_of_not_le
      intro hge
      have : t.pattern[k]? = none := by
        apply Array.get?_len_le
        simp [pattern, hge]
      rw [this] at hx
      contradiction
    ⟨k+1, Nat.succ_lt_succ this⟩
  else if h : k ≠ 0 then
    have h1 : k-1 < k := Nat.pred_lt h
    have h2 : k-1 < t.size := Nat.lt_of_lt_of_le h1 (Nat.le_of_lt_succ hk)
    let k' := t.toArray[k-1].2
    have hk' : k' < k := Nat.lt_of_le_of_lt (t.valid h2) h1
    step t x ⟨k', Nat.lt_trans hk' hk⟩
  else
    ⟨0, Nat.zero_lt_succ _⟩
termination_by _ k => k.val

/-- Extend a prefix table by one element

  If `t` is the prefix table for `xs` then `t.extend x` is the prefix table for `xs.push x`.
-/
def PrefixTable.extend [BEq α] (t : PrefixTable α) (x : α) : PrefixTable α where
  toArray := t.toArray.push (x, t.step x ⟨t.size, Nat.lt_succ_self _⟩)
  valid := by
    intros
    rw [Array.get_push]
    split
    next => exact t.valid ..
    next i h₁ h₂ =>
      have heq : i = t.size := by
        apply Nat.le_antisymm
        · apply Nat.le_of_lt_succ
          rwa [Array.size_push] at h₁
        · exact Nat.le_of_not_lt h₂
      rw [heq, ← Nat.lt_succ]
      exact Fin.isLt ..

/-- Make prefix table from a pattern array -/
def mkPrefixTable [BEq α] (xs : Array α) : PrefixTable α :=
  if h : xs.size = 0 then ⟨#[], fun .⟩ else
    have : xs.size-1 < xs.size := Nat.pred_lt h
    (mkPrefixTable xs.pop).extend xs[xs.size-1]
termination_by _ xs => xs.size

/-- Make prefix table from a pattern stream -/
partial def mkPrefixTableOfStream [BEq α] [Stream σ α] (stream : σ) : PrefixTable α :=
  loop ⟨#[], fun .⟩ stream
where
  /-- Inner loop for `mkPrefixTableOfStream` -/
  loop (t : PrefixTable α) (stream : σ) :=
    match Stream.next? stream with
    | none => t
    | some (x, stream) => loop (t.extend x) stream

/-- KMP matcher structure -/
structure Matcher (α) where
  /-- Prefix table for the pattern -/
  table : PrefixTable α
  /-- Current longest matching prefix -/
  state : Fin (table.size+1) := 0

/-- Make a KMP matcher for a given  pattern array -/
def Matcher.ofArray [BEq α] (pat : Array α) : Matcher α where
  table := mkPrefixTable pat

/-- Make a KMP matcher for a given a pattern stream -/
def Matcher.ofStream [BEq α] [Stream σ α] (pat : σ) : Matcher α where
  table := mkPrefixTableOfStream pat

/-- Find next match from a given stream

  Runs the stream until it reads a sequence that matches the sought pattern, then returns the stream
  state at that point and an updated matcher state.
-/
partial def Matcher.next? [BEq α] [Stream σ α] (m : Matcher α) (stream : σ) :
  Option (σ × Matcher α) :=
  match Stream.next? stream with
  | none => none
  | some (x, stream) =>
    let state := m.table.step x m.state
    if state = m.table.size then
      some (stream, {m with state := state})
    else
      next? {m with state := state} stream

end Array
