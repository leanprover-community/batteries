/-
Copyright (c) 2024 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: François G. Dorais
-/

namespace Stream

/-- Successor relation on streams. -/
inductive Next [Stream σ α] : σ → σ → Prop
  /-- `Next` constructor. -/
  | next : next? s = some (x, t) → Next t s

/-- Well founded stream class. -/
protected class WF (σ : Type _) (α : outParam (Type _)) extends Stream σ α where
  /-- Stream is accessible. -/
  acc s : Acc toStream.Next s

/-- `WellFoundedRelation` instance for well founded streams. -/
instance (priority := low) (σ α) [Stream.WF σ α] : WellFoundedRelation σ where
  wf := .intro Stream.WF.acc

macro_rules | `(tactic| decreasing_trivial) => `(tactic| apply Stream.Next.next; assumption)

/-! ### Recursors -/

/-- Recursor for well founded stream type. -/
@[elab_as_elim] def recWF [Stream.WF σ α] {motive : σ → Sort _}
    (init : {s : σ} → next? s = none → motive s)
    (next : {s t : σ} → {x : α} → next? s = some (x, t) → motive t → motive s)
    (s : σ) : motive s :=
  match h : next? s with
  | none => init h
  | some (x, t) => next h (recWF init next t)
termination_by s

/-- Recursor for well founded stream type. -/
@[elab_as_elim, inline] def recWFOn [Stream.WF σ α] {motive : σ → Sort _} (s : σ)
    (init : {s : σ} → next? s = none → motive s)
    (next : {s t : σ} → {x : α} → next? s = some (x, t) → motive t → motive s) : motive s :=
  recWF init next s

/-- Recursor for well founded stream type. -/
@[elab_as_elim, inline] def casesWFOn [Stream.WF σ α] {motive : σ → Sort _} (s : σ)
    (init : {s : σ} → next? s = none → motive s)
    (next : {s t : σ} → {x : α} → next? s = some (x, t) → motive s) : motive s :=
  recWF init (fun h _ => next h) s

/-! ### ForIn -/

/-- `forIn` implementation for well founded streams. -/
@[inline] def WF.forIn [Monad m] [Stream.WF σ α] (s : σ) (init : β) (f : α → β → m (ForInStep β)) :
    m β := loop init s
where
  /-- Inner loop for `WF.forIn` -/
  @[specialize] loop y s :=
    match _hint : next? s with
    | none => return y
    | some (x, t) =>
      f x y >>= fun
        | .done y => return y
        | .yield y => loop y t
termination_by s

/-- `ForIn` instance for well founded streams. -/
instance (priority := low+1) [Stream.WF σ α] : ForIn m σ α where
  forIn := WF.forIn

/-! ### toList -/

/-- Extract a list from a well founded stream. -/
def toList [Stream.WF σ α] (s : σ) : List α :=
  match _hint : next? s with
  | none => []
  | some (x, t) => x :: toList t
termination_by s

theorem toList_init [Stream.WF σ α] {s : σ} (h : next? s = none) :
  toList s = [] := by rw [toList, h]

theorem toList_next [Stream.WF σ α] {s t : σ} (h : next? s = some (x, t)) :
    toList s = x :: toList t := by rw [toList, h]

/-- Tail recursive implementation of `Stream.toList`. -/
private def toListTR [Stream.WF σ α] (s : σ) : List α :=
  loop [] s
where
  loop l s :=
    match _hint : next? s with
    | none => l.reverse
    | some (x, t) => loop (x :: l) t
termination_by s

private theorem toListTR_loop [Stream.WF σ α] (s : σ) (l : List α) :
    toListTR.loop l s = l.reverse ++ toList s := by
  induction s using Stream.recWF generalizing l with rw [toListTR.loop, h]
  | init h => simp [toList_init h]
  | next h ih => simp [toList_next h, ih]

@[csimp] private theorem toList_eq_toListTR : @toList = @toListTR := by
  funext; simp [toListTR, toListTR_loop]

/-! ### Basic instances -/

/-- Well founded stream from a well founded relation. -/
def WF.ofSubrelation [Stream σ α] (wf : WellFoundedRelation σ)
    (h : ∀ {s t}, Next s t → wf.rel s t) : Stream.WF σ α where
  acc s := Subrelation.accessible h (wf.wf.apply s)

/-- Well founded stream from a measure. -/
def WF.ofMeasure [Stream σ α] (m : σ → Nat) (h : ∀ {s t}, Next s t → m s < m t) : Stream.WF σ α :=
  WF.ofSubrelation (measure m) h

/-- Bounded stream type. -/
structure Bounded (σ : Type _) [Stream σ α] where
  /-- Underlying stream of a bounded stream. -/
  stream : σ
  /-- Fuel of a bounded stream. -/
  fuel : Nat

/-- Stream instance for bounded streams. -/
local instance (σ α) [Stream σ α] : Stream (Bounded σ) α where
  next?
  | ⟨_, 0⟩ => none
  | ⟨s, n+1⟩ =>
    match next? s with
    | none => none
    | some ⟨x, s⟩ => some ⟨x, s, n⟩

/-- Well founded stream instance for bounded streams. -/
instance (σ α) [Stream σ α] : Stream.WF (Bounded σ) α := WF.ofMeasure Bounded.fuel <| by
  intro _ _ h
  cases h with
  | next h =>
    simp [next?] at h
    split at h
    · contradiction
    · split at h
      · contradiction
      · cases h; simp

/-- Well founded stream instance for `List`. -/
instance (α) : Stream.WF (List α) α := WF.ofSubrelation inferInstance <| by
  intro _ _ h
  cases h with
  | next h =>
    simp only [next?] at h
    split at h
    · contradiction
    · injections; decreasing_tactic

/-- Well founded stream instance for `Substring`. -/
instance : Stream.WF Substring Char := WF.ofMeasure Substring.bsize <| by
  intro _ t h
  cases h with
  | next h =>
    simp [next?] at h
    match h with
    | ⟨_, _, h⟩ =>
      have := String.lt_next t.str t.startPos
      simp only [Substring.bsize, ← h, Nat.sub_eq, gt_iff_lt]
      omega

/-- Stream instance for `String.Iterator`. -/
local instance : Stream String.Iterator Char where
  next? s :=
    if h : s.hasNext then
      some (s.curr' h, s.next' h)
    else
      none

/-- Well founded stream instance for `String.Iterator`. -/
instance : Stream.WF String.Iterator Char :=
  WF.ofMeasure (fun s => s.s.endPos.byteIdx - s.i.byteIdx) <| by
  intro _ t h
  cases h with
  | next h =>
    simp [next?] at h
    match h with
    | ⟨hlt, _, h⟩ =>
      have := String.lt_next t.s t.i
      simp [String.Iterator.hasNext] at hlt
      simp [← h, String.Iterator.next']
      omega

/-- Well founded stream instance for `Subarray`. -/
instance (α) : Stream.WF (Subarray α) α := WF.ofMeasure Subarray.size <| by
  intro _ _ h
  cases h with
  | next h =>
    simp [next?] at h
    match h with
    | ⟨_, _, h⟩ =>
      simp only [← h, Subarray.size]
      omega

/-- Stream instance for `ByteArray.Iterator`. -/
local instance : Stream ByteArray.Iterator UInt8 where
  next? b :=
    if h : b.hasNext then
      some (b.curr' h, b.next' h)
    else
      none

/-- Well founded stream instance for `ByteArray.Iterator`. -/
instance : Stream.WF ByteArray.Iterator UInt8 := WF.ofMeasure (fun b => b.array.size - b.idx) <| by
  intro _ _ h
  cases h with
  | next h =>
    simp [next?] at h
    match h with
    | ⟨hlt, _, h⟩ =>
      simp [ByteArray.Iterator.hasNext] at hlt
      simp only [← h, ByteArray.Iterator.next']
      omega
