/-
Copyright (c) 2025 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: François G. Dorais
-/
import Batteries.Data.Stream.Basic
import Batteries.Data.Stream.Finite

/-! # Stream Combinators -/

namespace Stream

/-! ## Constant -/

/-- Constant stream with value `x`.

```
next? (const 'a') = ('a', const 'a')
```
-/
structure Constant {α : Type _} (x : α)
deriving DecidableEq

instance (x : α) : Stream (Constant x) α where
  next? _ := some (x, ⟨⟩)

@[inherit_doc Constant]
abbrev const (x : α) : Constant x := ⟨⟩

@[simp] theorem next?_const_eq : next? (const x) = some (x, const x) := rfl

/-! ## TakeUpTo -/

/-- Restrict a given stream to a maximum number of values.

```
toList (takeUpTo 3 [1,2,3,4,5,6]) = [1,2,3]
toList (takeUpTo 3 [1,2]) = [1,2]
```
-/
structure TakeUpTo (σ α) [Stream σ α] where
  takeUpTo ::
  /-- Maximum amount of values. -/
  fuel : Nat
  /-- Underlying stream. -/
  stream : σ

export TakeUpTo (takeUpTo)

attribute [inherit_doc TakeUpTo] takeUpTo

instance [Stream σ α] : Stream.WellFounded (TakeUpTo σ α) α := {
  measure TakeUpTo.fuel with
  next?
  | ⟨0, _⟩ => none
  | ⟨f+1, s⟩ => match next? s with
    | none => none
    | some (x, t) => some (x, ⟨f, t⟩)
  rel_of_next?_eq_some h := by
    split at h
    · contradiction
    · split at h
      · contradiction
      · cases h; simp_wf
}

@[simp] theorem next?_takeUpTo_zero [Stream σ α] (s : σ) : next? (takeUpTo 0 s) = none := rfl

@[simp] theorem next?_takeUpTo_succ [Stream σ α] (s : σ) :
  next? (takeUpTo (n+1) s) = match next? s with
    | none => none
    | some (x, s') => some (x, takeUpTo n s') := rfl

theorem next?_takeUpTo_eq_none_of_next?_eq_none [Stream σ α] {s : σ} (h : next? s = none) :
    next? (takeUpTo n s) = none := by
  cases n <;> simp [next?, h]

theorem next?_takeUpTo_eq_some_of_next?_eq_some_of_ne_zero [Stream σ α] [NeZero n]
    {s : σ} (h : next? s = some (x, s')) :
    next? (takeUpTo n s) = some (x, takeUpTo (n-1) s') := by
  cases n
  · have := NeZero.ne 0; contradiction
  · simp [next?, h]

/-! ## Map -/

/-- Applies a function to each element of a stream.

```
toList (map (· ^ 2) [1,2,3,4,5]) = [1,4,9,16,25]
```
-/
structure Map (f : α → β) (σ) [Stream σ α] where
  /-- Underlying stream. -/
  stream : σ

@[inherit_doc Map]
abbrev map (f : α → β) [Stream σ α] (s : σ) : Map f σ := ⟨s⟩

instance [Stream σ α] (f : α → β) : Stream (Map f σ) β where
  next?
  | ⟨s⟩ => match next? s with
    | some (x, s) => some (f x, ⟨s⟩)
    | none => none

theorem next?_map_eq_some_of_next?_eq_some [Stream σ α] {s : σ} {f : α → β}
    (h : next? s = some (x, s')) : next? (map f s) = some (f x, map f s') := by
  simp [next?, h]

theorem next?_map_eq_none_of_next?_eq_none [Stream σ α] {s : σ} {f : α → β}
    (h : next? s = none) : next? (map f s) = none := by
  simp [next?, h]

instance (f : α → β) [WithNextRelation σ α] : WithNextRelation (Map f σ) β where
  rel | ⟨s⟩, ⟨s'⟩ => Next s s'
  rel_of_next?_eq_some {s _ s'} h := by
    simp only [next?] at h
    match s, s' with
    | ⟨s⟩, ⟨s'⟩ =>
      split at h
      · cases h; simp [next_of_next?_eq_some, *]
      · contradiction

instance [WithNextRelation σ α] (f : α → β) (s : σ) [Stream.Finite s] :
    Stream.Finite (map f s) where
  acc := InvImage.accessible Map.stream Finite.acc

instance [Stream.WellFounded σ α] (f : α → β) : Stream.WellFounded (Map f σ) β where
  wf := InvImage.wf Map.stream WellFounded.wf

/-! ## Union -/

/-- Union of two stream types with the same output type. -/
structure Union (σ τ α) [Stream σ α] [Stream τ α] where
  /-- Underlying stream. -/
  stream : Sum σ τ

@[match_pattern, inherit_doc Union]
abbrev Union.inl [Stream σ α] [Stream τ α] (s : σ) : Union σ τ α := ⟨.inl s⟩

@[match_pattern, inherit_doc Union]
abbrev Union.inr [Stream σ α] [Stream τ α] (t : τ) : Union σ τ α := ⟨.inr t⟩

instance [Stream σ α] [Stream τ α] : Stream (Union σ τ α) α where
  next?
  | .inl s => match next? s with
    | none => none
    | some (x, s) => some (x, .inl s)
  | .inr t => match next? t with
    | none => none
    | some (x, t) => some (x, .inr t)

theorem next?_inl_eq_none_of_next?_eq_none [Stream σ α] [Stream τ α] {s : σ}
    (h : next? s = none) : next? (.inl s : Union σ τ α) = none := by
  simp [next?, h]

theorem next?_inl_eq_some_of_next?_eq_some [Stream σ α] [Stream τ α] {s : σ}
    (h : next? s = some (x, s')) : next? (.inl s : Union σ τ α) = some (x, .inl s') := by
  simp [next?, h]

theorem next?_inr_eq_none_of_next?_eq_none [Stream σ α] [Stream τ α] {t : τ}
    (h : next? t = none) : next? (.inr t : Union σ τ α) = none := by
  simp [next?, h]

theorem next?_inr_eq_some_of_next?_eq_some [Stream σ α] [Stream τ α] {t : τ}
    (h : next? t = some (x, t')) : next? (.inr t : Union σ τ α) = some (x, .inr t') := by
  simp [next?, h]

instance [WithNextRelation σ α] [WithNextRelation τ α] :
    WithNextRelation (Union σ τ α) α where
  rel
  | .inl s₁, .inl s₂ => Next s₁ s₂
  | .inr t₁, .inr t₂ => Next t₁ t₂
  | _, _ => False
  rel_of_next?_eq_some {u₁ _ u₂} h := by
    simp only [next?] at h
    match u₁, u₂ with
    | .inl _, .inl _ | .inr _, .inr _ =>
      simp only at h
      split at h
      · contradiction
      · cases h; simp [next_of_next?_eq_some, *]
    | .inl _, .inr _ | .inr _, .inl _ =>
      simp only at h; split at h <;> cases h

@[instance]
protected theorem Union.finite_inl [WithNextRelation σ α] [WithNextRelation τ α] (s : σ)
    [Stream.Finite s] : Stream.Finite (inl s : Union σ τ α) := by
  apply Finite.mk
  apply Acc.intro
  intro
  | inr _, h => simp [Next, WithNextRelation.rel] at h
  | inl s', h =>
    simp only [Next, WithNextRelation.rel] at h
    have : Stream.Finite s' := .ofNext h
    have : Stream.Finite (inl s' : Union σ τ α) := Union.finite_inl s'
    apply Finite.acc
 termination_by Finite.wrap s

@[instance]
protected theorem Union.finite_inr [WithNextRelation σ α] [WithNextRelation τ α] (t : τ)
    [Stream.Finite t] : Stream.Finite (inr t : Union σ τ α) := by
  apply Finite.mk
  apply Acc.intro
  intro
  | inl _, h => simp [Next, WithNextRelation.rel] at h
  | inr t', h =>
    simp only [Next, WithNextRelation.rel] at h
    have : Stream.Finite t' := .ofNext h
    have : Stream.Finite (inr t' : Union σ τ α) := Union.finite_inr t'
    apply Finite.acc
 termination_by Finite.wrap t

instance [Stream.WellFounded σ α] [Stream.WellFounded τ α] :
    Stream.WellFounded (Union σ τ α) α where
  wf := .intro fun | .inl _ | .inr _ => Finite.acc

/-! ## Concat -/

/-- Concatenate two streams one after the other.

```
toList (concat [1,2,3] [4,5]) = [1,2,3,4,5]
```
-/
structure Concat (σ τ α) [Stream σ α] [Stream τ α] where
  concat ::
  /-- First stream. -/
  fst : σ
  /-- Second stream. -/
  snd : τ

export Concat (concat)

attribute [inherit_doc Concat] concat

instance [Stream σ α] [Stream τ α] : Stream (Concat σ τ α) α where
  next?
  | concat s t =>
    match next? s with
    | some (x, s) => some (x, concat s t)
    | none =>
      match next? t with
      | some (x, t) => some (x, concat s t)
      | none => none

instance [WithNextRelation σ α] [WithNextRelation τ α] :
    WithNextRelation (Concat σ τ α) α where
  rel
  | concat s₁ t₁, concat s₂ t₂ =>
    match next? s₂ with
    | some _ => Next s₁ s₂ ∧ t₁ = t₂
    | none => Next t₁ t₂ ∧ s₁ = s₂
  rel_of_next?_eq_some {c₁ _ c₂} h := by
    match c₁, c₂ with
    | concat s₁ t₁, concat s₂ t₂ =>
      simp only [next?] at h
      split at h
      · cases h; simp [next_of_next?_eq_some, *]
      · split at h
        · cases h; simp [next_of_next?_eq_some, *]
        · contradiction

private theorem Concat.finite_aux [WithNextRelation σ α] [WithNextRelation τ α]
    (s : σ) (t : τ) [Stream.Finite s] [Stream.Finite t] (h : next? s = none) :
    Stream.Finite (concat s t) := by
  apply Finite.mk
  apply Acc.intro
  intro
  | concat s' t', hn =>
    simp [Next, WithNextRelation.rel] at hn
    split at hn
    · simp [h] at *
    · have : Stream.Finite t' := .ofNext hn.1
      have := finite_aux s t' h
      rw [hn.2]
      exact Finite.acc
termination_by Finite.wrap t
decreasing_by exact hn.1 -- FIXME

@[instance]
protected theorem Concat.finite [WithNextRelation σ α] [WithNextRelation τ α]
    (s : σ) (t : τ) [Stream.Finite s] [Stream.Finite t] : Stream.Finite (concat s t) := by
  apply Finite.mk
  apply Acc.intro
  intro
  | concat s' t', hn =>
    simp [Next, WithNextRelation.rel] at hn
    split at hn
    · have : Stream.Finite s' := .ofNext hn.1
      have := Concat.finite s' t
      rw [hn.2]
      exact Finite.acc
    · next hs =>
      have : Stream.Finite t' := .ofNext hn.1
      have := Concat.finite_aux s t' hs
      rw [hn.2]
      exact Finite.acc
termination_by Finite.wrap s
decreasing_by exact hn.1 -- FIXME

instance [Stream.WellFounded σ α] [Stream.WellFounded τ α] :
    Stream.WellFounded (Concat σ τ α) α where
  wf := .intro fun | concat _ _ => Finite.acc

/-! ## Join -/

/-- Join a list of streams one after the other.

```
toList (join [[1,2],[3,4,5],[6]]) = [1,2,3,4,5,6]
```
-/
structure Join (σ α) [Stream σ α] where
  join ::
  /-- List of streams. -/
  streams : List σ

export Join (join)

attribute [inherit_doc Join] join

private def Join.next? [Stream σ α] : Join σ α → Option (α × Join σ α)
  | ⟨[]⟩ => none
  | ⟨s :: l⟩ =>
    match Stream.next? s with
    | some (x, s) => some (x, ⟨s :: l⟩)
    | none => Join.next? ⟨l⟩

instance [Stream σ α] : Stream (Join σ α) α where
  next? := Join.next?

@[simp] theorem next?_join_nil_eq_none [Stream σ α] : next? (join [] : Join σ α) = none := by
  simp [next?, Join.next?]

theorem next?_join_cons_eq_some_of_next?_eq_some [Stream σ α] {s : σ} (h : next? s = some (x, s')):
    next? (join (s :: l)) = some (x, join (s' :: l)) := by
  simp [next?, Join.next?, h]

theorem next?_join_cons_eq_of_next?_eq_none [Stream σ α] {s : σ} (h : next? s = none):
    next? (join (s :: l)) = next? (join l) := by
  simp [next?, Join.next?, h]

private def Join.Next [WithNextRelation σ α] : Join σ α → Join σ α → Prop
  | _, join [] => False
  | join l₁, join (s₂ :: l₂) =>
    match Stream.next? s₂ with
    | none => Join.Next (join l₁) (join l₂)
    | some _ =>
      match l₁ with
      | [] => False
      | s₁ :: l₁ => l₁ = l₂ ∧ Stream.Next s₁ s₂

private def Join.next_of_next?_eq_some [WithNextRelation σ α] {j₁ j₂ : Join σ α} {x : α} :
    Stream.next? j₁ = some (x, j₂) → Join.Next j₂ j₁ := by
  intro h
  match j₁, j₂ with
  | join [], _ => simp [Stream.next?, Join.next?] at h
  | join (s₁ :: l₁), join l₂ =>
    simp [Stream.next?, Join.next?] at h
    split at h
    · next hs =>
      cases h
      rw [Join.Next.eq_def]
      simp [hs, Stream.next_of_next?_eq_some]
    · next hs =>
      rw [Join.Next.eq_def]
      simp [hs, Join.next_of_next?_eq_some h]

instance [WithNextRelation σ α] : WithNextRelation (Join σ α) α where
  rel := Join.Next
  rel_of_next?_eq_some := Join.next_of_next?_eq_some

instance [WithNextRelation σ α] : Stream.Finite (join (σ := σ) (α := α) []) where
  acc := by
    apply Acc.intro
    intro _ h
    simp [Next, WithNextRelation.rel, Join.Next] at h

@[instance]
protected theorem Join.finite_cons [WithNextRelation σ α] (s : σ) (l : List σ)
    [Stream.Finite s] [Stream.Finite (join l)] : Stream.Finite (join (s :: l)) := by
  apply Finite.mk
  apply Acc.intro
  intro
  | join l', h =>
    simp only [Stream.Next, WithNextRelation.rel] at h
    rw [Join.Next.eq_def] at h
    simp only at h
    split at h
    · next hs =>
      have : Stream.Finite (join l') := .ofNext h
      exact Finite.acc
    · next hs =>
      split at h
      · contradiction
      · next s' l' =>
        simp only [h.1, true_and] at h ⊢
        have : Stream.Finite s' := .ofNext h
        have : Stream.Finite (join (s' :: l)) := Join.finite_cons s' l
        exact Finite.acc
termination_by Finite.wrap s
decreasing_by exact h.2 -- FIXME

instance [Stream.WellFounded σ α] : Stream.WellFounded (Join σ α) α where
  wf := .intro fun
    | join l => by
      induction l with
      | nil => exact Finite.acc
      | cons s l ih =>
        have : Stream.Finite (join l) := ⟨ih⟩
        exact Finite.acc

/-! ## Zip -/

/-- Zip two streams together.

```
toList (zip [1,2,3] ['a','b','c','d','e']) = [(1, 'a'), (2, 'b'), (3, 'c')]
```
-/
structure Zip (σ τ α β) [Stream σ α] [Stream τ β] where
  zip ::
  /-- First stream. -/
  fst : σ
  /-- Second stream. -/
  snd : τ

export Zip (zip)

attribute [inherit_doc Zip] zip

instance [Stream σ α] [Stream τ β] : Stream (Zip σ τ α β) (α × β) where
  next?
  | zip s t => match next? s, next? t with
    | some (x, s), some (y, t) => some ((x, y), zip s t)
    | _, _ => none

theorem next?_zip_eq_some_of_next?_fst_eq_some_of_next?_snd_eq_some
    [Stream σ α] [Stream τ β] {s : σ} {t : τ}
    (hs : next? s = some (x, s')) (ht : next? t = some (y, t')) :
    next? (zip s t) = some ((x, y), zip s' t') := by
  simp [next?, *]

theorem next?_zip_eq_none_zip_of_next?_fst_eq_none
    [Stream σ α] [Stream τ β] {s : σ} {t : τ} (hs : next? s = none) :
    next? (zip s t) = none := by
  simp [next?, *]

theorem next?_zip_eq_none_zip_of_next?_snd_eq_none
    [Stream σ α] [Stream τ β] {s : σ} {t : τ} (ht : next? t = none) :
    next? (zip s t) = none := by
  simp [next?, *]

instance [WithNextRelation σ α] [WithNextRelation τ β] :
    WithNextRelation (Zip σ τ α β) (α × β) where
  rel | zip s₁ t₁, zip s₂ t₂ => Next s₁ s₂ ∧ Next t₁ t₂
  rel_of_next?_eq_some {z₁ _ z₂} h := by
    simp only [next?] at h
    match z₁, z₂ with
    | zip s₁ t₁, zip s₂ t₂ =>
      split at h
      · cases h; simp [next_of_next?_eq_some, *]
      · contradiction

instance [WithNextRelation σ α] [WithNextRelation τ β] {s : σ} {t : τ}
    [Stream.Finite s] : Stream.Finite (zip s t) where
  acc :=
    have ac : Acc (fun | zip s₁ _, zip s₂ _ => Next s₁ s₂) (zip s t) :=
      InvImage.accessible Zip.fst Finite.acc
    Subrelation.accessible (ac := ac) <| by
      intro | zip _ _, zip _ _, h => exact h.1

instance [WithNextRelation σ α] [WithNextRelation τ β] {s : σ} {t : τ}
    [Stream.Finite t] : Stream.Finite (zip s t) where
  acc :=
    have ac : Acc (fun | zip _ t₁, zip _ t₂ => Next t₁ t₂) (zip s t) :=
      InvImage.accessible Zip.snd Finite.acc
    Subrelation.accessible (ac := ac) <| by
      intro | zip _ _, zip _ _, h => exact h.2

instance [Stream.WellFounded σ α] [WithNextRelation τ β] :
    Stream.WellFounded (Zip σ τ α β) (α × β) where
  wf := .intro fun | zip _ _ => Finite.acc

instance [WithNextRelation σ α] [Stream.WellFounded τ β] :
    Stream.WellFounded (Zip σ τ α β) (α × β) where
  wf := .intro fun | zip _ _ => Finite.acc
