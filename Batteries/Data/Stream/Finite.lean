/-
Copyright (c) 2025 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: François G. Dorais
-/
import Batteries.Data.Stream.Basic
import Batteries.Data.ByteSubarray
import Batteries.WF

/-! # Finite and Well-Founded Streams

This file defines two main classes:

- `Stream.Finite` provides a proof that a specific stream is finite.
- `Stream.WellFounded` extends the `Stream` class and provides an instance of `Stream.Finite` for
  every stream of the given type.

The importance of these classes is that iterating along a finite stream is guaranteed to terminate.
Therefore, it is possible to prove facts about such iterations.

The `Stream.WellFounded` class is easiest to use: match on `Stream.next?` and provide a termination
hint. The general pattern is this:
```
def foo [Stream.WellFounded σ α] (s : σ) : β :=
  match _hint : Stream.next? s with
  | none => _
  | some (x, t) => _
termination_by s
```
(The underscore in `_hint` is only to avoid the unused variable linter from complaining.)

The `Stream.Finite` class is more general but is slightly trickier to use.
```
def foo [Stream σ α] (s : σ) [Stream.Finite s] : β :=
  match hint : Stream.next? s with
  | none => _
  | some (x, t) =>
    have : Stream.Finite t := .ofSome hint
    _
termination_by Stream.Finite.wrap s
```
Several examples of this pattern can be found below. We hope to avoid the need for the extra `have`
at some point in the future.

## Constructing `Stream.WellFounded` Classes

TODO

## Constructing `Stream.Finite` Classes

TODO

-/

namespace Stream

/-- Class to define the next relation of a stream type. -/
class WithNextRelation (σ : Type _) (α : outParam <| Type _) extends Stream σ α where
  /-- Next relation for a stream type `σ`. -/
  rel : σ → σ → Prop -- this is named `rel` to match `WellFoundedRelatiom`
  /-- Next relation extends the default. -/
  rel_of_next?_eq_some : next? s = some (x, t) → rel t s

/-- Default next relation for a stream type. -/
instance (priority := low) defaultNextRelation (σ) [Stream σ α] : WithNextRelation σ α where
  rel t s := ∃ x, next? s = some (x, t)
  rel_of_next?_eq_some h := ⟨_, h⟩

/-- Next relation for a stream. -/
abbrev Next [WithNextRelation σ α] : σ → σ → Prop := WithNextRelation.rel

/-- Next relation, restricted to a subset of streams. -/
abbrev RestrictedNext [WithNextRelation σ α] (p : σ → Prop) (s t : σ) : Prop :=
  p t ∧ Next s t

theorem next_of_next?_eq_some [WithNextRelation σ α] {s t : σ} :
    next? s = some (x, t) → Next t s := WithNextRelation.rel_of_next?_eq_some

/-- Class for well-founded stream type. -/
class WellFounded.{u,v} (σ : Type u) (α : outParam <| Type v) extends
  WithNextRelation σ α, WellFoundedRelation σ

/-- Define a well-founded stream type instance from a well-founded relation. -/
def WellFounded.ofRelation.{u,v} [Stream.{u,v} σ α] [inst : WellFoundedRelation σ]
    (h : {s t : σ} → {x : α} → next? s = (x, t) → WellFoundedRelation.rel t s) :
    Stream.WellFounded σ α := { inst with rel_of_next?_eq_some := h }

/-- Define a well-founded stream type instance from a measure. -/
def WellFounded.ofMeasure.{u,v} [Stream.{u,v} σ α] (f : σ → Nat)
    (h : {s t : σ} → {x : α} → next? s = (x, t) → f t < f s) :
    Stream.WellFounded σ α := { measure f with rel_of_next?_eq_some := h }

macro_rules
| `(tactic| decreasing_trivial) => `(tactic| apply Stream.next_of_next?_eq_some; assumption)

instance (α) : WellFounded (List α) α :=
  .ofMeasure List.length <| by
    intro _ _ _ h
    simp only [next?] at h
    split at h
    · contradiction
    · cases h; simp

instance : WellFounded Substring Char :=
  .ofMeasure Substring.bsize <| by
    intro _ _ _ h
    simp only [next?] at h
    split at h
    · next hlt =>
      cases h
      simp only [Substring.bsize, String.next, String.pos_add_char, Nat.sub_eq]
      apply Nat.sub_lt_sub_left hlt
      apply Nat.lt_add_of_pos_right
      exact Char.utf8Size_pos _
    · contradiction

instance (α) : WellFounded (Subarray α) α :=
  .ofMeasure Subarray.size <| by
    intro _ _ _ h
    simp only [next?] at h
    split at h
    · cases h
      simp only [Subarray.size, Subarray.stop, Subarray.start]
      apply Nat.sub_one_lt
      apply Nat.sub_ne_zero_of_lt
      assumption
    · contradiction

instance : WellFounded Batteries.ByteSubarray UInt8 :=
  .ofMeasure Batteries.ByteSubarray.size <| by
    intro _ _ _ h
    simp only [next?, bind, Option.bind] at h
    split at h
    · contradiction
    · next heq =>
      rw [getElem?_def] at heq
      split at heq
      · next hpos =>
        cases h
        simp only [Batteries.ByteSubarray.size, Batteries.ByteSubarray.popFront] at hpos ⊢
        split
        · next heq =>
          simp [heq] at hpos
        · simp
          apply Nat.sub_one_lt
          exact Nat.ne_zero_of_lt hpos
      · contradiction
      done

instance : WellFounded Std.Range Nat :=
  .ofMeasure (fun r => r.stop - r.start) <| by
    intro _ _ _ h
    simp only [next?] at h
    split at h
    · next hlt =>
      cases h
      apply Nat.sub_lt_sub_left hlt
      apply Nat.lt_add_of_pos_right
      exact Std.Range.step_pos _
    · contradiction

section StreamIterator
open Std.Iterators

private theorem IsPlausibleSuccessorOf_eq (σ α) [Stream σ α] :
    IterM.IsPlausibleSuccessorOf (m := Id) (α := StreamIterator σ α) =
      InvImage (fun s s' : σ => ∃ x, next? s' = some (x, s)) (·.internalState.stream) := by
  funext i₁ i₂
  simp only [IterM.IsPlausibleSuccessorOf, IterM.IsPlausibleStep, InvImage, eq_iff_iff]
  constructor
  · intro
    | ⟨.yield i x, heq, h⟩ =>
      cases heq
      exact h
  · intro ⟨x, h⟩
    exact ⟨.yield i₁ x, rfl, ⟨x, h⟩⟩

instance (σ α) [wf : Stream.WellFounded σ α] : Finite (α := StreamIterator σ α) Id where
  wf := by
    rw [IsPlausibleSuccessorOf_eq]
    refine InvImage.wf _ ?_
    refine Subrelation.wf ?_ wf.wf
    intro _ _ ⟨_, h⟩
    exact next_of_next?_eq_some h

end StreamIterator

/-- Class for a finite stream of type `σ`. -/
class Finite [WithNextRelation σ α] (s : σ) : Prop where
  /-- A finite stream is accessible with respect to the `Next` relation. -/
  acc : Acc Next s

instance [WellFounded σ α] (s : σ) : Finite s where
  acc := match WellFounded.wf (σ := σ) with | ⟨h⟩ => h s

namespace Finite

/-- Predecessor of a finite stream is finite. -/
theorem ofNext [WithNextRelation σ α] {s t : σ} [Finite s] (h : Next t s) : Finite t where
  acc := match acc (s := s) with | ⟨_, a⟩ => a _ h

/-- Predecessor of a finite stream is finite. -/
theorem ofSome [WithNextRelation σ α] {s t : σ} [Finite s] (h : next? s = some (x, t)) :
  Finite t := .ofNext <| next_of_next?_eq_some h

/-- Define a finite stream instance for a restricted subset of streams. -/
theorem ofRestrictedNext.{u,v} [WithNextRelation.{u,v} σ α] {p : σ → Prop}
    (H : ∀ {s t}, Next s t → p t → p s) (h : p s) (acc : Acc (RestrictedNext p) s) : Finite s where
  acc :=
    Subrelation.accessible (fun h₁ h₂ => ⟨H h₁ h₂, h₂, h₁⟩) (Acc.restriction p acc h)

/-- Wrap a finite stream into a well-founded type for use in termination proofs. -/
def wrap [WithNextRelation σ α] (s : σ) [Finite s] : { s : σ // Acc Next s } :=
  ⟨s, Finite.acc⟩

end Finite

/-- Folds a monadic function over a finite stream from left to right. -/
@[inline, specialize]
def foldlM [Monad m] [WithNextRelation σ α] (s : σ) [Finite s] (f : β → α → m β)
    (init : β) : m β :=
  match h : next? s with
  | none => pure init
  | some (x, t) =>
    have : Finite t := .ofSome h
    f init x >>= foldlM t f
termination_by Finite.wrap s

theorem foldlM_none [Monad m] [WithNextRelation σ α] {s : σ} [Finite s]
    {f : β → α → m β} (h : next? s = none) : foldlM s f init = pure init := by
  simp only [foldlM]
  split <;> simp_all

theorem foldlM_some [Monad m] [WithNextRelation σ α] {s t : σ} [Finite s] [Finite t]
    {f : β → α → m β} (h : next? s = some (x, t)) : foldlM s f init = f init x >>= foldlM t f := by
  simp only [foldlM]
  split
  · simp_all
  · next heq =>
    simp only [h, Option.some.injEq, Prod.mk.injEq] at heq
    cases heq.1; cases heq.2; rfl

/-- Folds a monadic function over a finite stream from right to left. -/
@[specialize]
def foldrM [Monad m] [WithNextRelation σ α] (s : σ) [Finite s] (f : α → β → m β)
    (init : β) : m β :=
  match h : next? s with
  | none => pure init
  | some (x, t) =>
    have : Finite t := .ofSome h
    foldrM t f init >>= f x
termination_by Finite.wrap s

theorem foldrM_none [Monad m] [WithNextRelation σ α] {s : σ} [Finite s]
    {f : α → β → m β} (h : next? s = none) : foldrM s f init = pure init := by
  rw [foldrM]; split <;> simp_all

theorem foldrM_some [Monad m] [WithNextRelation σ α] {s t : σ} [Finite s] [Finite t]
    {f : α → β → m β} (h : next? s = some (x, t)) : foldrM s f init = foldrM t f init >>= f x := by
  rw [foldrM]; split <;> simp_all

/-- Folds a function over a finite stream from left to right. -/
@[specialize]
def foldl [WithNextRelation σ α] (s : σ) [Finite s] (f : β → α → β) (init : β) : β :=
  match h : next? s with
  | none => init
  | some (x, t) =>
    have : Finite t := .ofSome h
    foldl t f (f init x)
termination_by Finite.wrap s

theorem foldl_none [WithNextRelation σ α] {s : σ} [Finite s] {f : β → α → β}
    (h : next? s = none) : foldl s f init = init := by
  rw [foldl]; split <;> simp_all

theorem foldl_some [WithNextRelation σ α] {s t : σ} [Finite s] [Finite t] {f : β → α → β}
    (h : next? s = some (x, t)) : foldl s f init = foldl t f (f init x) := by
  rw [foldl]; split <;> simp_all

/-- Folds a function over a finite stream from right to left. -/
@[specialize]
def foldr [WithNextRelation σ α] (s : σ) [Finite s] (f : α → β → β) (init : β) : β :=
  match h : next? s with
  | none => init
  | some (x, t) =>
    have : Finite t := .ofSome h
    f x <| foldr t f init
termination_by Finite.wrap s

theorem foldr_none [WithNextRelation σ α] {s : σ} [Finite s]
    {f : α → β → β} (h : next? s = none) : foldr s f init = init := by
  rw [foldr]
  split <;> simp_all

theorem foldr_some [WithNextRelation σ α] {s t : σ} [Finite s] [Finite t]
    {f : α → β → β} (h : next? s = some (x, t)) : foldr s f init = f x (foldr t f init) := by
  rw [foldr]
  split <;> simp_all

/-- Extract the length of a finite stream. -/
@[inline]
def length [WithNextRelation σ α] (s : σ) [Finite s] : Nat :=
  foldl s (fun l _ => l + 1) 0

theorem length_none [WithNextRelation σ α] {s : σ} [Finite s]
    (h : next? s = none) : length s = 0 := foldl_none h

private theorem length_aux [WithNextRelation σ α] {s : σ} [Finite s] :
    foldl s (fun l _ => l + 1) n = foldl s (fun l _ => l + 1) 0 + n := by
  match h : next? s with
  | none => simp [foldl_none h]
  | some (x, t) =>
    have : Finite t := .ofSome h
    conv => lhs; rw [foldl_some h, length_aux]
    conv => rhs; rw [foldl_some h, length_aux]
    simp +arith
termination_by Finite.wrap s

theorem length_some [WithNextRelation σ α] {s t : σ} [Finite s] [Finite t]
    (h : next? s = some (x, t)) : length s = length t + 1 := by
  simp [length, foldl_some h, length_aux (n := 1)]

/-- Extract the sequence of values of a finite stream as a `List` in reverse order. -/
@[inline]
def toListRev [WithNextRelation σ α] (s : σ) [Finite s] : List α :=
  foldl s (fun r x => x :: r) []

theorem toListRev_none [WithNextRelation σ α] {s : σ} [Finite s]
    (h : next? s = none) : toListRev s = [] := by
  simp [toListRev, foldl_none h]

private theorem toListRev_aux [WithNextRelation σ α] {s : σ} [Finite s] :
    foldl s (fun r x => x :: r) l = foldl s (fun r x => x :: r) [] ++ l := by
  match h : next? s with
  | none => simp [foldl_none h]
  | some (x, t) =>
    have : Finite t := .ofSome h
    conv => lhs; rw [foldl_some h, toListRev_aux]
    conv => rhs; rw [foldl_some h, toListRev_aux]
    simp
termination_by Finite.wrap s

theorem toListRev_some [WithNextRelation σ α] {s t : σ} [Finite s] [Finite t]
    (h : next? s = some (x, t)) : toListRev s = toListRev t ++ [x] := by
  simp [toListRev, foldl_some h, toListRev_aux (l := [x])]

/-- Extract the sequence of values of a finite stream as a `List`. -/
@[inline]
def toList [WithNextRelation σ α] (s : σ) [Finite s] : List α :=
  toListRev s |>.reverse

theorem toList_none [WithNextRelation σ α] {s : σ} [Finite s]
    (h : next? s = none) : toList s = [] := by
  simp [toList, toListRev_none h]

theorem toList_some [WithNextRelation σ α] {s t : σ} [Finite s] [Finite t]
    (h : next? s = some (x, t)) : toList s = x :: toList t := by
  simp [toList, toListRev_some h]

/-- Extract the sequence of values of a finite stream as an `Array`. -/
@[inline]
def toArray [WithNextRelation σ α] (s : σ) [Finite s] : Array α :=
  foldl s Array.push #[]

theorem toArray_none [WithNextRelation σ α] {s : σ} [Finite s]
    (h : next? s = none) : toArray s = #[] := by
  simp [toArray, foldl_none h]

private theorem toArray_aux [WithNextRelation σ α] {s : σ} [Finite s] :
    foldl s Array.push l = l ++ foldl s Array.push #[] := by
  match h : next? s with
  | none => simp [foldl_none h]
  | some (x, t) =>
    have : Finite t := .ofSome h
    conv => lhs; rw [foldl_some h, toArray_aux]
    conv => rhs; rw [foldl_some h, toArray_aux]
    simp
termination_by Finite.wrap s

theorem toArray_some [WithNextRelation σ α] {s t : σ} [Finite s] [Finite t]
    (h : next? s = some (x, t)) : toArray s = #[x] ++ toArray t := by
  simp [toArray, foldl_some h, toArray_aux (l := #[x])]

theorem toArray_toList_eq_toArray [WithNextRelation σ α] {s : σ} [Finite s] :
    (toList s).toArray = toArray s := by
  match h : next? s with
  | none => simp [toList_none h, toArray_none h]
  | some (x, t) =>
    have : Finite t := .ofSome h
    simp only [toList_some h, toArray_some h]
    rw [List.toArray_cons, toArray_toList_eq_toArray]
termination_by Finite.wrap s

@[simp] theorem toList_eq_self (l : List α) : toList l = l := by
  induction l with
  | nil => rw [toList_none rfl]
  | cons x l ih => rw [toList_some rfl, ih]
