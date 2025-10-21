/-
Copyright (c) 2023 F. G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: F. G. Dorais
-/

namespace Array

/-- Prefix table for the Knuth-Morris-Pratt matching algorithm

  This is an array of the form `t = [(x₀,n₀), (x₁,n₁), (x₂, n₂), ...]` where for each `i`, `nᵢ` is
  the length of the longest proper prefix of `xs = [x₀,x₁,...,xᵢ]` which is also a suffix of `xs`.
-/
structure PrefixTable (α : Type _) extends Array (α × Nat) where
  /-- Validity condition to help with termination proofs -/
  valid : (h : i < toArray.size) → toArray[i].2 ≤ i

instance : Inhabited (PrefixTable α) where
  default := ⟨#[], nofun⟩

/-- Returns the size of the prefix table -/
abbrev PrefixTable.size (t : PrefixTable α) := t.toArray.size

/-- Transition function for the KMP matcher

  Assuming we have an input `xs` with a suffix that matches the pattern prefix `t.pattern[:len]`
  where `len : Fin (t.size+1)`. Then `xs.push x` has a suffix that matches the pattern prefix
  `t.pattern[:t.step x len]`. If `len` is as large as possible then `t.step x len` will also be
  as large as possible.
-/
def PrefixTable.step [BEq α] (t : PrefixTable α) (x : α) : Fin (t.size+1) → Fin (t.size+1)
  | ⟨k, hk⟩ =>
    let cont := fun () =>
      match k with
      | 0 => ⟨0, Nat.zero_lt_succ _⟩
      | k + 1 =>
        have h2 : k < t.size := Nat.lt_of_succ_lt_succ hk
        let k' := t.toArray[k].2
        have hk' : k' < k + 1 := Nat.lt_succ_of_le (t.valid h2)
        step t x ⟨k', Nat.lt_trans hk' hk⟩
    if hsz : k < t.size then
      if x == t.toArray[k].1 then
        ⟨k+1, Nat.succ_lt_succ hsz⟩
      else cont ()
    else cont ()
termination_by k => k.val

/-- Extend a prefix table by one element

  If `t` is the prefix table for `xs` then `t.extend x` is the prefix table for `xs.push x`.
-/
def PrefixTable.extend [BEq α] (t : PrefixTable α) (x : α) : PrefixTable α where
  toArray := t.toArray.push (x, t.step x ⟨t.size, Nat.lt_succ_self _⟩)
  valid _ := by
    rw [Array.getElem_push]
    split
    · exact t.valid ..
    · next h => exact Nat.le_trans (Nat.lt_succ.1 <| Fin.isLt ..) (Nat.not_lt.1 h)

/-- Make prefix table from a pattern array -/
def mkPrefixTable [BEq α] (xs : Array α) : PrefixTable α := xs.foldl (·.extend) default

/-- Make prefix table from a pattern stream -/
partial def mkPrefixTableOfStream [BEq α] [Std.Stream σ α] (stream : σ) : PrefixTable α :=
  loop default stream
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
  state : Fin (table.size + 1) := 0

/-- Make a KMP matcher for a given pattern array -/
def Matcher.ofArray [BEq α] (pat : Array α) : Matcher α where
  table := mkPrefixTable pat

/-- Make a KMP matcher for a given a pattern stream -/
def Matcher.ofStream [BEq α] [Std.Stream σ α] (pat : σ) : Matcher α where
  table := mkPrefixTableOfStream pat

/-- Find next match from a given stream

  Runs the stream until it reads a sequence that matches the sought pattern, then returns the stream
  state at that point and an updated matcher state.
-/
partial def Matcher.next? [BEq α] [Std.Stream σ α] (m : Matcher α) (stream : σ) :
    Option (σ × Matcher α) :=
  match Stream.next? stream with
  | none => none
  | some (x, stream) =>
    let state := m.table.step x m.state
    if state = m.table.size then
      some (stream, { m with state })
    else
      next? { m with state } stream

namespace Matcher
open Std.Iterators

/-- Iterator transformer for KMP matcher. -/
protected structure Iterator (σ n α) [BEq α] (m : Matcher α) [Iterator σ n α] where
  /-- Inner iterator. -/
  inner : IterM (α := σ) n α
  /-- Matcher state. -/
  state : Fin (m.table.size + 1) := 0

private def modifyStep [BEq α] (m : Matcher α) [Iterator σ n α]
    (it : IterM (α := m.Iterator σ n α) n σ) :
    it.internalState.inner.Step (α := σ) → IterStep (IterM (α := m.Iterator σ n α) n σ) σ
  | .done _ => .done
  | .skip it' _ => .skip ⟨{it.internalState with inner := it'}⟩
  | .yield it' x _ =>
    let state := m.table.step x m.state
    if state = m.table.size then
      .yield ⟨{inner := it', state := state}⟩ it'.internalState
    else
      .skip ⟨{inner := it', state := state}⟩

instance [Monad n] [BEq α] (m : Matcher α) [Iterator σ n α] :
    Iterator (m.Iterator σ n α) n σ where
  IsPlausibleStep it step := ∃ step', m.modifyStep it step' = step
  step it := it.internalState.inner.step >>=
    fun step => pure (.deflate ⟨m.modifyStep _ _, step.inflate, rfl⟩)

private def finitenessRelation [Monad n] [BEq α] (m : Matcher α) [Iterator σ n α] [Finite σ n] :
    FinitenessRelation (m.Iterator σ n α) n where
  rel := InvImage IterM.IsPlausibleSuccessorOf fun it => it.internalState.inner
  wf := InvImage.wf _ Finite.wf
  subrelation {it it'} h := by
    obtain ⟨_, hsucc, step, rfl⟩ := h
    simp only [IterM.Step] at step
    cases step with simp only [IterStep.successor, modifyStep, reduceCtorEq] at hsucc
    | skip =>
      cases hsucc
      apply IterM.isPlausibleSuccessorOf_of_skip
      assumption
    | yield =>
      split at hsucc
      · next heq =>
        cases hsucc
        split at heq
        · cases heq
          apply IterM.isPlausibleSuccessorOf_of_yield
          assumption
        · contradiction
      · next heq =>
        cases hsucc
        split at heq
        · contradiction
        · cases heq
          apply IterM.isPlausibleSuccessorOf_of_yield
          assumption
      · contradiction

instance [Monad n] [BEq α] (m : Matcher α) [Iterator σ n α] [inst : Finite σ n] :
    Finite (m.Iterator σ n α) n (β := σ) := .of_finitenessRelation m.finitenessRelation

end Matcher

end Array
