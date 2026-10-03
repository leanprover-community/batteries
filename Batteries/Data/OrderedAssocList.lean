/-
Copyright (c) 2023 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module
public import Batteries.Data.AssocList
import all Batteries.Data.AssocList
public import Batteries.Classes.Order

/-!
# Ordered association lists

`OrderedAssocList` is a wrapper around `AssocList`,
with the additional invariant that the keys are in strictly increasing order.

As a consequence, an `OrderedAssocList` is determined by the lookup function `l[x]?`, that is
`(∀ a, l₁[a]? = l₂[a]?) → l₁ = l₂`
and this makes proving identities between operations much easier than with `AssocList`.

As the operations on `OrderedAssocList` are defined in terms of `AssocList`,
they evaluate in the kernel, but inherit the `O(n)` time complexity
(i.e. are not suitable for large data). Their advantage relative to an ordered map is the
simple extensionality property above.

We will later add another wrapper requiring that a "default" value does not appear,
so e.g. finitely supported functions can be uniquely represented.

The main operations defined are:
* `l[x]?`, which linearly searches the list, stopping if the keys get too large.
* `insert`, which inserts a new key-value pair, maintaining the order invariant.
* `filterMapVal f`, for `f : α → β → Option γ`, which applies a function to values,
  dropping some values.
* `merge f` for `f : α → Option β → Option γ → Option δ` which merges two lists,
  dropping some values. It runs in time `O(l₁.length + l₂.length)`.
-/

@[expose] public section

open Std

namespace Batteries

/-!
We first define some predicates and operations in the `AssocList` namespace.

* `KeysOrdered cmp l` asserts that the keys of an `l : AssocList` are strictly increasing
  with respect to a comparator `cmp`.
* `LTHeadKey cmp a l` asserts that `a` is less than (according to `cmp`) the first key of `l`,
  or that `l` is empty.
-/

namespace AssocList

/-- The head key of an `AssocList`, or `none` if the list is empty. -/
def headKey? (l : AssocList α β) : Option α :=
  match l with
  | .nil => none
  | .cons a _ _ => some a

@[simp] theorem headKey?_nil : headKey? (.nil : AssocList α β) = none := rfl
@[simp] theorem headKey?_cons : headKey? (.cons a b t) = some a := rfl

theorem headKey?_eq_head? (l : AssocList α β) : l.headKey? = l.toList.head?.map Prod.fst := by
  cases l <;> rfl

/--
The condition that an element is less than the first key of an `AssocList`, or that list is empty.
-/
abbrev LTHeadKey (cmp : α → α → Ordering) (a : α) (t : AssocList α β) : Prop :=
  match headKey? t with | none => True | some x => cmp a x = .lt

@[simp] theorem ltHeadKey_nil {cmp : α → α → Ordering} :
    LTHeadKey cmp a (.nil : AssocList α β) = True := rfl
@[simp] theorem ltHeadKey_cons : LTHeadKey cmp a (.cons x y t) = (cmp a x = .lt) := rfl

theorem ltHeadKey_iff {l : AssocList α β} :
    LTHeadKey cmp a l ↔ ∀ p ∈ l.toList.head?, cmp a p.1 = .lt := by
  cases l <;> simp

/--
The predicate that the keys of an `AssocList` are
in strictly increasing order according to the comparator `cmp`.
-/
def KeysOrdered (cmp : α → α → Ordering) : AssocList α β → Prop
  | .nil => True
  | .cons a _ t => LTHeadKey cmp a t ∧ KeysOrdered cmp t

@[simp] theorem keysOrdered_cons_nil : KeysOrdered cmp (.cons a b nil) := ⟨trivial, trivial⟩

theorem keysOrdered_iff_pairwise {α : Type u} {β : Type v} {cmp : α → α → Ordering}
    [TransCmp cmp] {l : AssocList α β} :
    KeysOrdered cmp l ↔ l.toList.Pairwise (fun p q : α × β => cmp p.1 q.1 = .lt) := by
  induction l with
  | nil => simp [KeysOrdered]
  | cons a b t ih =>
    simp only [KeysOrdered, toList, List.pairwise_cons, ih, ltHeadKey_iff]
    refine ⟨fun ⟨hlt, hp⟩ => ⟨fun q hq => ?_, hp⟩, fun ⟨hall, hp⟩ => ⟨fun q hq => ?_, hp⟩⟩
    · match t, hq with
      | .cons x y s, hq =>
        rcases List.mem_cons.mp hq with rfl | hq
        · exact hlt _ rfl
        · exact TransCmp.lt_trans (hlt _ rfl) (List.rel_of_pairwise_cons hp hq)
    · exact hall _ (List.mem_of_mem_head? hq)

theorem KeysOrdered.tail (h : KeysOrdered cmp (.cons a b t)) : KeysOrdered cmp t := h.2

theorem KeysOrdered.lt_of_mem {α : Type u} {β : Type v} {cmp : α → α → Ordering} [TransCmp cmp]
    {x : α} {y : β} {t : AssocList α β} (h : KeysOrdered cmp (cons x y t))
    {p : α × β} (hp : p ∈ t.toList) : cmp x p.1 = .lt := by
  have := keysOrdered_iff_pairwise.mp h
  simp only [toList, List.pairwise_cons] at this
  exact this.1 p hp

theorem KeysOrdered.ltHeadKey (w : KeysOrdered cmp (cons a b t)) : LTHeadKey cmp a t :=
  w.1

theorem ltHeadKey_of_cons [TransCmp cmp] (w : LTHeadKey cmp a (cons x y t))
    (h : KeysOrdered cmp (cons x y t)) :
    LTHeadKey cmp a t := by
  have h := h.ltHeadKey
  revert w h
  dsimp [LTHeadKey]
  split
  · simp
  · exact TransCmp.lt_trans

theorem ltHeadKey_of_le [TransCmp cmp] (h : cmp x a ≠ .gt) (w : LTHeadKey cmp a t) :
    LTHeadKey cmp x t := by
  revert w
  dsimp [LTHeadKey]
  split
  · simp
  · exact TransCmp.lt_of_le_of_lt h

/--
A relation on two `AssocList`s, asserting that the head key of the first list is at most
the head key of the second list, or that the second list is empty.
-/
abbrev LEHeadKey
    (cmp : α → α → Ordering) (s : AssocList α β) (t : AssocList α γ) : Prop :=
  match s.headKey?, t.headKey? with
  | some a₁, some a₂ => cmp a₁ a₂ ≠ .gt
  | none, some _ => False
  | _, none => True

@[simp] theorem leHeadKey_cons_cons :
    LEHeadKey cmp (cons a b t) (cons x y s) = (cmp a x ≠ .gt) := rfl

theorem leHeadKey_iff {s : AssocList α β} {t : AssocList α γ} :
    LEHeadKey cmp s t ↔ ∀ q ∈ t.toList.head?, ∃ p ∈ s.toList.head?, cmp p.1 q.1 ≠ .gt := by
  cases s <;> cases t <;> simp [LEHeadKey]

theorem ltHeadKey_of_leHeadKey [TransCmp cmp]
    (w : LTHeadKey cmp a s) (h : LEHeadKey cmp s t) :
    LTHeadKey cmp a t := by
  dsimp [LTHeadKey, LEHeadKey] at *
  revert h w
  match headKey? s, headKey? t with
  | some a, some b => exact TransCmp.lt_of_lt_of_le
  | some a, none => intros; trivial
  | none, some b => simp
  | none, none => intros; trivial

theorem leHeadKey_cons [TransCmp cmp]
    (h : KeysOrdered cmp (cons x y t)) (w : LEHeadKey cmp t s) :
    LEHeadKey cmp (cons x y t) s := by
  have p := h.ltHeadKey
  dsimp [LTHeadKey, LEHeadKey] at *
  revert p w
  match headKey? s, headKey? t with
  | some a, some b =>
    intro p w
    simp [TransCmp.lt_of_lt_of_le w p]
  | some a, none => intros; trivial
  | none, some b => simp
  | none, none => intros; trivial

theorem KeysOrdered.cons {cmp : α → α → Ordering}
    (w : LTHeadKey cmp a t) (h : KeysOrdered cmp t) :
    KeysOrdered cmp (.cons a b t) := ⟨w, h⟩

theorem find?_eq_none_of_ltHeadKey {cmp : α → α → Ordering} [TransCmp cmp] [BEq α] [LawfulBEq α]
    (w : LTHeadKey cmp a l) (h : KeysOrdered cmp l) :
    l.find? a = none := by
  match l with
  | nil => rfl
  | cons x y t =>
    rw [find?]
    split
    · simp_all [ReflCmp.compare_self]
    · exact find?_eq_none_of_ltHeadKey (ltHeadKey_of_cons w h) h.tail

/-!
# Ordered-respecting operations on `AssocList`

We now define `orderedInsert`, and `orderedMerge`,
which will later be wrapped as `OrderedAssocList.insert` and `OrderedAssocList.merge`.

We prove that with `KeysOrdered` input these functions produce `KeysOrdered` outputs.
We prove the same about `AssocList.filterMapVal`.
-/

/--
Insert a key-value pair into an `AssocList`,
in such a way that if the original list has keys in increasing order,
so does the result.
(Otherwise, it is inserted before the first key the new key is smaller than,
or replaces the first key the new key is equal to.)

We later wrap this as `OrderedAssocList.insert`.
-/
def orderedInsert (cmp : α → α → Ordering) (l : AssocList α β) (a : α) (b : β) : AssocList α β :=
  match l with
  | .nil => .cons a b .nil
  | .cons x y t => match _w : cmp a x with
    | .lt => .cons a b l
    | .eq => .cons a b t
    | .gt => .cons x y (orderedInsert cmp t a b)

@[simp] theorem orderedInsert_nil : (nil : AssocList α β).orderedInsert cmp a b = .cons a b nil :=
  rfl

@[simp] theorem orderedInsert_cons :
    orderedInsert cmp (.cons x y t) a b = match _w : cmp a x with
    | .lt => .cons a b (.cons x y t)
    | .eq => .cons a b t
    | .gt => .cons x y (orderedInsert cmp t a b) := rfl

theorem headKey?_orderedInsert {l : AssocList α β} :
    headKey? (orderedInsert cmp l a b) =
      match headKey? l with
        | none => some a
        | some x => match cmp a x with | .lt | .eq => some a | .gt => some x := by
  match l with
  | .nil => rfl
  | .cons x _ _ => dsimp [headKey?, orderedInsert]; cases cmp a x <;> rfl

theorem headKey?_orderedInsert_or (cmp) (l : AssocList α β) (a) (b) :
    headKey? (orderedInsert cmp l a b) = some a ∨
      headKey? (orderedInsert cmp l a b) = headKey? l := by
  rw [headKey?_orderedInsert]
  match l with
  | .nil => left; rfl
  | .cons x y s => dsimp; cases cmp a x <;> simp

mutual
theorem KeysOrdered.orderedInsert_aux [LawfulEqCmp cmp] [OrientedCmp cmp] {x y t}
    (h : KeysOrdered cmp (AssocList.cons x y t)) (w : cmp a x = Ordering.gt) :
    KeysOrdered cmp (AssocList.cons x y (AssocList.orderedInsert cmp t a b)) := by
        apply KeysOrdered.cons
        · dsimp [LTHeadKey]
          rcases AssocList.headKey?_orderedInsert_or cmp t a b with (p|p)
          · rw [p]
            exact OrientedCmp.lt_of_gt w
          · rw [p]
            exact h.ltHeadKey
        · apply KeysOrdered.orderedInsert
          exact h.tail

theorem KeysOrdered.orderedInsert [LawfulEqCmp cmp] [OrientedCmp cmp] (h : KeysOrdered cmp l) :
    KeysOrdered cmp (AssocList.orderedInsert cmp l a b) := by
  match l with
  | .nil => trivial
  | .cons x y t =>
    dsimp [AssocList.orderedInsert]
    match w : cmp a x with
    | .lt => exact ⟨w, h⟩
    | .eq =>
      rcases LawfulEqCmp.eq_of_compare w with rfl
      exact h
    | .gt => exact h.orderedInsert_aux w
end

theorem toList_orderedInsert {α : Type u} {β : Type v} {cmp : α → α → Ordering}
    [LawfulEqCmp cmp] [TransCmp cmp] {l : AssocList α β} (h : KeysOrdered cmp l) (a : α) (b : β) :
    (orderedInsert cmp l a b).toList =
      l.toList.filter (fun p => cmp a p.1 == .gt) ++
        (a, b) :: l.toList.filter (fun p => cmp a p.1 == .lt) := by
  induction l with
  | nil => simp
  | cons x y t ih =>
    have tail_lt : ∀ p ∈ t.toList, cmp x p.1 = .lt := fun _ hp => h.lt_of_mem hp
    simp only [orderedInsert_cons, toList, List.filter_cons]
    match w : cmp a x with
    | .lt =>
      have all_lt : ∀ p ∈ t.toList, cmp a p.1 = .lt :=
        fun p hp => TransCmp.lt_trans w (tail_lt p hp)
      have e1 : t.toList.filter (fun p => cmp a p.1 == .gt) = [] :=
        List.filter_eq_nil_iff.mpr fun p hp => by simp [all_lt p hp]
      have e2 : t.toList.filter (fun p => cmp a p.1 == .lt) = t.toList :=
        List.filter_eq_self.mpr fun p hp => by simp [all_lt p hp]
      simp [e1, e2]
    | .eq =>
      obtain rfl := LawfulEqCmp.eq_of_compare w
      have e1 : t.toList.filter (fun p => cmp a p.1 == .gt) = [] :=
        List.filter_eq_nil_iff.mpr fun p hp => by simp [tail_lt p hp]
      have e2 : t.toList.filter (fun p => cmp a p.1 == .lt) = t.toList :=
        List.filter_eq_self.mpr fun p hp => by simp [tail_lt p hp]
      simp [e1, e2]
    | .gt => simp [ih h.tail]

theorem leHeadKey_filterMapVal [TransCmp cmp] (h : KeysOrdered cmp l) :
    LEHeadKey cmp l (l.filterMapVal f) := by
  match l with
  | .nil => simp [LEHeadKey]
  | .cons x y t =>
    simp [filterMapVal]
    match f x y with
    | none =>
      exact leHeadKey_cons h (leHeadKey_filterMapVal h.tail)
    | some _ => simp [ReflCmp.compare_self]

theorem KeysOrdered.filterMapVal [TransCmp cmp] (h : KeysOrdered cmp l) :
    KeysOrdered cmp (l.filterMapVal f) := by
  match l with
  | .nil => exact h
  | .cons x y t =>
    simp only [AssocList.filterMapVal]
    split
    · exact h.tail.filterMapVal
    · apply KeysOrdered.cons
      · exact ltHeadKey_of_leHeadKey h.ltHeadKey
          (leHeadKey_filterMapVal h.tail)
      · exact h.tail.filterMapVal

/--
Merge two `AssocList`s,
at each stage taking the first key-value pair from whichever list has a smaller first key.
If both inputs have keys in strictly increasing order, so does the result.
(We later wrap this as `OrderedAssocList.merge`.)

We combine values using a function `f : α → Option β → Option γ → Option δ` which we call as
`f a (some b) none` when encountering a key present only in the first list (with value `b`),
`f a none (some g)` when encountering a key present only in the second list (with value `g`), and
`f a (some b) (some g)` when encountering a key present in both lists.
(Note the value of `f a none none` is never used.)
-/
def orderedMerge (cmp : α → α → Ordering) (f : α → Option β → Option γ → Option δ) :
    AssocList α β → AssocList α γ → AssocList α δ
  | .nil, .nil => nil
  | .nil, .cons a₂ g t₂ => filterMapVal (fun a g => f a none (some g)) (.cons a₂ g t₂)
  | .cons a₁ b t₁, .nil => filterMapVal (fun a b => f a (some b) none) (.cons a₁ b t₁)
  | .cons a₁ b t₁, .cons a₂ g t₂ => match cmp a₁ a₂ with
    | .lt => match (f a₁ (some b) none) with
      | some d => .cons a₁ d (orderedMerge cmp f t₁ (.cons a₂ g t₂))
      | none => orderedMerge cmp f t₁ (.cons a₂ g t₂)
    | .eq => match (f a₁ (some b) (some g)) with
      | some d => .cons a₁ d (orderedMerge cmp f t₁ t₂)
      | none => orderedMerge cmp f t₁ t₂
    | .gt => match (f a₂ none (some g)) with
      | some d => .cons a₂ d (orderedMerge cmp f (.cons a₁ b t₁) t₂)
      | none => orderedMerge cmp f (.cons a₁ b t₁) t₂
termination_by l₁ l₂ => l₁.length + l₂.length

theorem ltHeadKey_orderedMerge [TransCmp cmp]
    (h₁ : LTHeadKey cmp a l₁) (h₂ : LTHeadKey cmp a l₂)
    (w₁ : KeysOrdered cmp l₁) (w₂ : KeysOrdered cmp l₂) :
    LTHeadKey cmp a (orderedMerge cmp f l₁ l₂) := by
  match l₁, l₂ with
  | .nil, .nil => simp [orderedMerge]
  | .nil, .cons a₂ g t₂ =>
    rw [orderedMerge]
    exact ltHeadKey_of_leHeadKey h₂ (leHeadKey_filterMapVal w₂)
  | .cons a₁ b t₁, .nil =>
    rw [orderedMerge]
    exact ltHeadKey_of_leHeadKey h₁ (leHeadKey_filterMapVal w₁)
  | .cons a₁ b t₁, .cons a₂ g t₂ =>
    rw [orderedMerge]
    match cmp a₁ a₂ with
    | .lt =>
      dsimp
      split
      · exact h₁
      · exact ltHeadKey_orderedMerge (ltHeadKey_of_cons h₁ w₁) h₂ w₁.tail w₂
    | .eq =>
      dsimp
      split
      · exact h₁
      · exact ltHeadKey_orderedMerge (ltHeadKey_of_cons h₁ w₁) (ltHeadKey_of_cons h₂ w₂)
          w₁.tail w₂.tail
    | .gt =>
      dsimp
      split
      · exact h₂
      · exact ltHeadKey_orderedMerge h₁ (ltHeadKey_of_cons h₂ w₂) w₁ w₂.tail

theorem KeysOrdered.orderedMerge [LawfulEqCmp cmp] [TransCmp cmp]
    (h₁ : KeysOrdered cmp l₁) (h₂ : KeysOrdered cmp l₂) :
    KeysOrdered cmp (AssocList.orderedMerge cmp f l₁ l₂) := by
  match l₁, l₂ with
  | .nil, .nil => rw [AssocList.orderedMerge]; trivial
  | .nil, .cons a₂ g t₂ =>
    rw [AssocList.orderedMerge]
    exact h₂.filterMapVal
  | .cons a₁ b t₁, .nil =>
    rw [AssocList.orderedMerge]
    exact h₁.filterMapVal
  | .cons a₁ b t₁, .cons a₂ g t₂ =>
    rw [AssocList.orderedMerge]
    match h : cmp a₁ a₂ with
    | .lt => match (f a₁ (some b) none) with
      | some d =>
        apply KeysOrdered.cons
        · apply ltHeadKey_orderedMerge h₁.ltHeadKey (ltHeadKey_cons.mpr h)
            h₁.tail h₂
        · exact h₁.tail.orderedMerge h₂
      | none => exact h₁.tail.orderedMerge h₂
    | .eq => match (f a₁ (some b) (some g)) with
      | some d =>
        dsimp
        apply KeysOrdered.cons
        · rcases (LawfulEqCmp.eq_of_compare h) with rfl
          exact ltHeadKey_orderedMerge h₁.ltHeadKey
            h₂.ltHeadKey h₁.tail h₂.tail
        · exact h₁.tail.orderedMerge h₂.tail
      | none => exact h₁.tail.orderedMerge h₂.tail
    | .gt => match (f a₂ none (some g)) with
      | some d =>
        apply KeysOrdered.cons
        · apply ltHeadKey_orderedMerge (ltHeadKey_cons.mpr (OrientedCmp.lt_of_gt h))
            h₂.ltHeadKey h₁ h₂.tail
        · exact h₁.orderedMerge h₂.tail
      | none => exact h₁.orderedMerge h₂.tail

/--
Find the value associated to a key by traversing left to right,
short-circuiting once we are considering larger keys.
-/
def orderedFind? (cmp : α → α → Ordering) (l : AssocList α β) (x : α) : Option β :=
  match l with
  | .nil => none
  | .cons a b t => match cmp x a with
    | .lt => none
    | .eq => some b
    | .gt => orderedFind? cmp t x

@[simp] theorem orderedFind?_nil {cmp : α → α → Ordering} :
    orderedFind? cmp (nil : AssocList α β) x = none := rfl

theorem orderedFind?_eq_find?
    {cmp : α → α → Ordering} [LawfulEqCmp cmp] [TransCmp cmp] [BEq α] [LawfulBEq α]
    (l : AssocList α β) (h : l.KeysOrdered cmp) (x : α) : l.orderedFind? cmp x = l.find? x := by
  match l with
  | .nil => rfl
  | .cons a b t =>
    rw [find?, AssocList.orderedFind?]
    split
    · split
      · simp_all [ReflCmp.compare_self]
      · rw [AssocList.find?_eq_none_of_ltHeadKey (cmp := cmp)]
        · exact AssocList.ltHeadKey_of_le (by simp_all)
            h.ltHeadKey
        · exact h.tail
    · simp_all [LawfulEqCmp.eq_of_compare ‹_›]
    · split
      · simp_all [ReflCmp.compare_self]
      · apply orderedFind?_eq_find? _ h.tail

theorem orderedFind?_eq
    {cmp : α → α → Ordering} [LawfulEqCmp cmp] [TransCmp cmp] [BEq α] [LawfulBEq α]
    (l : AssocList α β) (h : l.KeysOrdered cmp) (x : α) :
    l.orderedFind? cmp x = (l.toList.find? (·.1 == x)).map (·.2) := by
  rw [orderedFind?_eq_find? l h, find?_eq]

theorem orderedFind?_eq_none_of_ltHeadKey (l : AssocList α β) (w : LTHeadKey cmp x l) :
    orderedFind? cmp l x = none := by
  match l with
  | .nil => rfl
  | .cons a b t =>
    match p : cmp x a with
    | .lt => simp [orderedFind?, p]
    | .eq => simp_all [LTHeadKey]
    | .gt => simp_all [LTHeadKey]

theorem orderedFind?_cons [TransCmp cmp]
    (h : (AssocList.cons a b t).KeysOrdered cmp) :
    orderedFind? cmp (.cons a b t) x = if cmp x a = .eq then some b else orderedFind? cmp t x := by
  simp only [AssocList.orderedFind?]
  split <;> rename_i w <;> simp only [w, reduceCtorEq, reduceIte]
  rw [AssocList.orderedFind?_eq_none_of_ltHeadKey]
  simp only [LTHeadKey, headKey?]
  split <;> rename_i h'
  · trivial
  · apply TransCmp.lt_trans w
    revert h'
    split
    · simp
    · simp only [Option.some.injEq]
      rintro rfl
      exact h.1

@[simp] theorem orderedFind?_cons_self [OrientedCmp cmp] :
    orderedFind? cmp (.cons a b t) a = some b := by
  simp [AssocList.orderedFind?, ReflCmp.compare_self]

theorem orderedFind?_orderedInsert {cmp : α → α → Ordering} [LawfulEqCmp cmp] [TransCmp cmp]
    (l : AssocList α β) (h : KeysOrdered cmp l) (a : α) (b : β) :
    (orderedInsert cmp l a b).orderedFind? cmp x =
      if cmp x a = .eq then some b else l.orderedFind? cmp x := by
  match l with
  | .nil =>
    simp only [orderedInsert, orderedFind?_cons, keysOrdered_cons_nil]
  | .cons a' b' t =>
    simp only [orderedInsert_cons]
    split <;> rename_i h₁
    · apply orderedFind?_cons
      exact ⟨h₁, h⟩
    · rcases LawfulEqCmp.eq_of_compare h₁
      rw [orderedFind?_cons h, orderedFind?_cons]
      · split <;> rfl
      · exact h
    · rw [orderedFind?_cons, orderedFind?_orderedInsert t h.tail, orderedFind?_cons h]
      · split <;> rename_i h₂
        · rcases (LawfulEqCmp.eq_of_compare h₂).symm
          simp_all [OrientedCmp.lt_of_gt]
        · rfl
      · exact h.orderedInsert_aux h₁
termination_by l.length

theorem orderedFind?_orderedInsert_self {cmp : α → α → Ordering} [LawfulEqCmp cmp] [TransCmp cmp]
    (l : AssocList α β) (h : KeysOrdered cmp l)  (a : α) (b : β) :
    (orderedInsert cmp l a b).orderedFind? cmp a = some b := by
  simp [h, orderedFind?_orderedInsert, ReflCmp.compare_self]

/--
If two `AssocList`s have ordered keys
we can check whether they are equal by checking if their `orderedFind?` functions are equal.
-/
theorem ext_orderedFind?
    (cmp : α → α → Ordering) [LawfulEqCmp cmp] [TransCmp cmp]
    {l₁ l₂ : AssocList α β} (h₁ : l₁.KeysOrdered cmp) (h₂ : l₂.KeysOrdered cmp)
    (w : ∀ a, l₁.orderedFind? cmp a = l₂.orderedFind? cmp a) : l₁ = l₂ := by
  match w₁ : l₁, w₂ : l₂ with
  | .nil, .nil => rfl
  | .cons a b t, .nil =>
    exfalso
    specialize w a
    simp_all
  | .nil, .cons a b t =>
    exfalso
    specialize w a
    simp_all
  | .cons a₁ b₁ t₁, .cons a₂ b₂ t₂ =>
    match h : cmp a₁ a₂ with
    | .lt =>
      exfalso
      have w₂ : l₂.orderedFind? cmp a₁ = none := by
        rw [w₂, orderedFind?_eq_none_of_ltHeadKey _ h]
      specialize w a₁
      simp [orderedFind?_cons_self] at w
      simp_all
    | .eq =>
      rcases LawfulEqCmp.eq_of_compare h
      have w' := w a₁
      simp only [orderedFind?_cons_self, Option.some.injEq] at w'
      congr
      apply ext_orderedFind? cmp h₁.tail h₂.tail
      intro a
      specialize w a
      rw [orderedFind?_cons h₁, orderedFind?_cons h₂] at w
      split at w <;> rename_i h
      · rcases LawfulEqCmp.eq_of_compare h
        rw [orderedFind?_eq_none_of_ltHeadKey, orderedFind?_eq_none_of_ltHeadKey]
        apply h₂.ltHeadKey
        apply h₁.ltHeadKey
      · exact w
    | .gt =>
      exfalso
      have w₁ : l₁.orderedFind? cmp a₂ = none := by
        rw [w₁, orderedFind?_eq_none_of_ltHeadKey _ (OrientedCmp.lt_of_gt h)]
      specialize w a₂
      simp [orderedFind?_cons_self] at w
      simp_all

@[simp]
theorem orderedFind?_filterMapVal {cmp : α → α → Ordering} [LawfulEqCmp cmp] [TransCmp cmp]
    {l : AssocList α β} (h : KeysOrdered cmp l) :
    (filterMapVal f l).orderedFind? cmp a = (l.orderedFind? cmp a).bind (fun b => f a b) := by
  -- This isn't true at the level of `AssocList`; we need uniqueness of keys.
  match l with
  | .nil => rfl
  | .cons x y t =>
    simp only [filterMapVal_cons, orderedFind?_cons, h]
    split
    · rw [orderedFind?_filterMapVal h.tail]
      split <;> rename_i h'
      · have h' := LawfulEqCmp.eq_of_compare h'
        rw [orderedFind?_eq_none_of_ltHeadKey]
        · simp_all
        · rcases h' with rfl
          exact h.ltHeadKey
      · rfl
    · rw [orderedFind?_cons]
      · split <;> rename_i h'
        · simp_all [LawfulEqCmp.eq_of_compare h']
        · rw [orderedFind?_filterMapVal h.tail]
      · exact KeysOrdered.cons
          (ltHeadKey_of_leHeadKey h.ltHeadKey
            (leHeadKey_filterMapVal h.tail))
          h.tail.filterMapVal
termination_by l.length

theorem filterMapVal_filterMapVal {cmp : α → α → Ordering} [LawfulEqCmp cmp] [TransCmp cmp]
    {f : α → γ → Option δ} {g : α → β → Option γ}
    {l : AssocList α β} (h : KeysOrdered cmp l) :
    filterMapVal f (filterMapVal g l) =
      filterMapVal (fun a b => (g a b).bind (fun c => f a c)) l := by
  apply ext_orderedFind? (cmp := cmp)
  · exact h.filterMapVal.filterMapVal
  · exact h.filterMapVal
  · intro a
    rw [orderedFind?_filterMapVal, orderedFind?_filterMapVal h, orderedFind?_filterMapVal h]
    · ext d
      simp only [Option.bind_eq_some_iff]
      constructor
      · rintro ⟨c, ⟨⟨b, hb, hc⟩, hd⟩⟩
        refine ⟨b, hb, c, hc, hd⟩
      · rintro ⟨b, hb, c, hc, hd⟩
        refine ⟨c, ⟨⟨b, hb, hc⟩, hd⟩⟩
    · exact h.filterMapVal

end AssocList

/--
An `OrderedAssocList` is an `AssocList` with the additional invariant that
the keys are in strictly increasing order according to some specified comparator function.
-/
structure OrderedAssocList {α : Type u} (cmp : α → α → Ordering) (β : Type v) where
  /-- The underlying `AssocList` of an `OrderedAssocList`. -/
  toAssocList : AssocList α β
  /-- The invariant that the keys are in strictly increasing order according to `cmp`. -/
  keysOrdered : toAssocList.KeysOrdered cmp

namespace OrderedAssocList

variable {α : Type u} {cmp : α → α → Ordering}

/-- The empty `OrderedAssocList`. -/
def nil : OrderedAssocList cmp β := ⟨.nil, trivial⟩

@[simp] theorem toAssocList_nil : (nil : OrderedAssocList cmp β).toAssocList = .nil := rfl

/-- The length of an `OrderedAssocList`. -/
def length (l : OrderedAssocList cmp β) : Nat := l.toAssocList.length

@[simp] theorem length_nil : length (nil : OrderedAssocList cmp β) = 0 := rfl
@[simp] theorem length_mk_cons : length ⟨.cons a b t, h⟩ = length ⟨t, h.tail⟩ + 1 :=
  rfl

/-- The first key-value pair in an `OrderedAssocList`. -/
def head? (l : OrderedAssocList cmp β) : Option (α × β) :=
  match l with
  | ⟨.nil, _⟩ => none
  | ⟨.cons a b _, _⟩ => some (a, b)

theorem head?_eq_head? (l : OrderedAssocList cmp β) : l.head? = l.toAssocList.toList.head? := by
  match l with
  | ⟨.nil, _⟩ => rfl
  | ⟨.cons _ _ _, _⟩ => rfl

/-- The tail of an `OrderedAssocList`. -/
def tail (l : OrderedAssocList cmp β) : OrderedAssocList cmp β :=
  match l with
  | ⟨.nil, _⟩ => l
  | ⟨.cons _ _ t, h⟩ => ⟨t, h.tail⟩

@[simp] theorem toAssocList_tail_mk_nil {h} :
    (tail (⟨.nil, h⟩ : OrderedAssocList cmp β)).toAssocList = .nil := rfl
@[simp] theorem toAssocList_tail_mk_cons {h} :
    (tail (⟨.cons a b t, h⟩ : OrderedAssocList cmp β)).toAssocList = t := rfl

@[simp] theorem length_tail : length (tail l) = length l - 1 := by
  match l with
  | ⟨.nil, _⟩ => rfl
  | ⟨.cons _ _ _, _⟩ => rfl

/--
Find the value associated to a key by traversing left to right,
short-circuiting once we are considering larger keys.

This is the internal implementation of  `l[x]?`, which should be preferred.
-/
def find? (l : OrderedAssocList cmp β) (x : α) : Option β :=
  l.toAssocList.orderedFind? cmp x

/-- Check if an `OrderedAssocList` contains a specific key. -/
def contains (l : OrderedAssocList cmp β) (x : α) : Bool := (l.find? x).isSome

instance : GetElem? (OrderedAssocList cmp β) α β (fun l a => l.contains a) where
  getElem? l a := l.find? a
  getElem l a h := (l.find? a).get h

@[simp] theorem getElem?_nil {x : α} : (nil : OrderedAssocList cmp β)[x]? = none := rfl
@[simp] theorem getElem?_mk_nil {x : α} : (⟨.nil, h⟩ : OrderedAssocList cmp β)[x]? = none := rfl

theorem contains_eq_isSome_getElem? {l : OrderedAssocList cmp β} :
    l.contains a = l[a]?.isSome := rfl

/-- The first key in an `OrderedAssocList`, or `none` if the list is empty. -/
def headKey? (l : OrderedAssocList cmp β) : Option α := l.toAssocList.headKey?

@[simp] theorem headKey?_nil : headKey? (nil : OrderedAssocList cmp β) = none := rfl
@[simp] theorem headKey?_mk_cons : headKey? ⟨.cons a b t, h⟩ = some a := rfl

/-- Either `a` is less than the first key of `l`, or `l` is empty. -/
def LTHeadKey (a : α) (l : OrderedAssocList cmp β) : Prop :=
  AssocList.LTHeadKey cmp a l.toAssocList

/-- The head key of a tail is either `none`, or greater than the original head key. -/
theorem ltHeadKey_tail (h : AssocList.KeysOrdered cmp (.cons a b t)) :
    LTHeadKey a ⟨t, h.tail⟩ := h.1

theorem getElem?_eq_none_of_ltHeadKey (l : OrderedAssocList cmp β) (w : LTHeadKey x l) :
    l[x]? = none :=
  AssocList.orderedFind?_eq_none_of_ltHeadKey _ w

theorem getElem?_mk_cons [TransCmp cmp]
    {h : (AssocList.cons a b t).KeysOrdered cmp} :
    (⟨.cons a b t, h⟩ : OrderedAssocList _ _)[x]? =
      if cmp x a = .eq then some b else (⟨t, h.tail⟩ : OrderedAssocList _ _)[x]? := by
  simp only [getElem?, find?, AssocList.orderedFind?]
  split <;> rename_i w <;> simp only [w, reduceCtorEq, reduceIte]
  rw [AssocList.orderedFind?_eq_none_of_ltHeadKey]
  have p := ltHeadKey_tail h
  revert p
  simp only [LTHeadKey, AssocList.LTHeadKey]
  split
  · trivial
  · exact TransCmp.lt_trans w

@[simp] theorem getElem?_mk_cons_self [OrientedCmp cmp]
    {h : (AssocList.cons a b t).KeysOrdered cmp} :
    (⟨.cons a b t, h⟩ : OrderedAssocList _ _)[a]? = some b := by
  simp [getElem?, find?, AssocList.orderedFind?, ReflCmp.compare_self]

theorem ext_toAssocList {l₁ l₂ : OrderedAssocList cmp β}
    (w : l₁.toAssocList = l₂.toAssocList) : l₁ = l₂ := by
  cases l₁; cases l₂; congr

@[ext] theorem ext [LawfulEqCmp cmp] [TransCmp cmp] {l₁ l₂ : OrderedAssocList cmp β}
    (w : ∀ a : α, l₁[a]? = l₂[a]?) : l₁ = l₂ := by
  apply ext_toAssocList
  apply AssocList.ext_orderedFind? _ l₁.keysOrdered l₂.keysOrdered
  simpa [getElem?, find?, AssocList.orderedFind?_eq_find?, l₁.keysOrdered, l₂.keysOrdered]
    using w

@[simp] theorem contains_nil : contains (nil : OrderedAssocList cmp β) x = false := rfl
@[simp] theorem contains_mk_cons_self [OrientedCmp cmp]
    {h : (AssocList.cons a b t).KeysOrdered cmp} :
    contains ⟨.cons a b t, h⟩ a = true := by
  rw [contains_eq_isSome_getElem?]
  simp

/--
Prepend a key-value pair,
requiring a proof that the key is smaller than the existing smallest key.
-/
def cons (a : α) (b : β) (l : OrderedAssocList cmp β) (w : LTHeadKey a l) :
    OrderedAssocList cmp β :=
  match l with
  | ⟨.nil, _⟩ => ⟨.cons a b .nil, AssocList.keysOrdered_cons_nil⟩
  | ⟨.cons x y t, h⟩ => ⟨.cons a b (.cons x y t), ⟨w, h⟩⟩

@[simp] theorem toAssocList_cons : (cons a b l w).toAssocList = .cons a b l.toAssocList := by
  dsimp [cons]
  match l with
  | ⟨.nil, _⟩ => rfl
  | ⟨.cons x y t, h⟩ => rfl

@[simp] theorem getElem?_cons [TransCmp cmp] {l : OrderedAssocList cmp β} {w} :
    (cons a b l w)[x]? = if cmp x a = .eq then some b else l[x]? := by
  simp only [cons]
  split <;> exact getElem?_mk_cons

@[simp] theorem headKey?_cons : headKey? (cons a b l w) = some a := by
  match l with
  | ⟨.nil, _⟩
  | ⟨.cons _ _ _, _⟩ => rfl

section insert
variable [LawfulEqCmp cmp]

section
variable [OrientedCmp cmp]

/--
Insert a key-value pair into an `OrderedAssocList`.
This replaces the current value if the key is already present,
and otherwise inserts it before the first key which is greater than the inserted key.
-/
def insert (l : OrderedAssocList cmp β) (a : α) (b : β) : OrderedAssocList cmp β :=
  ⟨l.toAssocList.orderedInsert cmp a b, l.keysOrdered.orderedInsert⟩

@[simp] theorem toAssocList_insert (l : OrderedAssocList cmp β) (a : α) (b : β) :
    (insert l a b).toAssocList = l.toAssocList.orderedInsert cmp a b := rfl

@[simp] theorem insert_mk_nil :
    insert (⟨.nil, h⟩ : OrderedAssocList cmp β) a b =
      ⟨.cons a b .nil, AssocList.keysOrdered_cons_nil⟩ := rfl

@[simp] theorem insert_mk_cons :
    insert (⟨.cons x y t, h⟩ : OrderedAssocList cmp β) a b = match w : cmp a x with
    | .lt => ⟨.cons a b (.cons x y t), ⟨w, h⟩⟩
    | .eq => ⟨.cons a b t, by
        cases (LawfulEqCmp.eq_of_compare w); exact h⟩
    | .gt => ⟨.cons x y (t.orderedInsert cmp a b),
        h.orderedInsert_aux w⟩ := by
  dsimp [insert, AssocList.orderedInsert]
  congr
  split <;> rfl

theorem length_insert_ne_zero {l : OrderedAssocList cmp β} : (insert l a b).length ≠ 0 := by
  match l with
  | ⟨.nil, _⟩ => simp
  | ⟨.cons x y t, _⟩ =>
    dsimp [insert, AssocList.orderedInsert, length]
    split <;> simp

end

variable [TransCmp cmp]

theorem getElem?_insert (l : OrderedAssocList cmp β) (a : α) (b : β) :
    (insert l a b)[x]? = if cmp x a = .eq then some b else l[x]? :=
  AssocList.orderedFind?_orderedInsert l.toAssocList l.keysOrdered a b

theorem getElem?_insert_self (l : OrderedAssocList cmp β) (a : α) (b : β) :
    (insert l a b)[a]? = some b := by
  simp [getElem?_insert, ReflCmp.compare_self]

theorem contains_insert (l : OrderedAssocList cmp β) (a : α) (b : β) :
    (l.insert a b).contains x = ((cmp x a = .eq) || l.contains x) := by
  rw [contains_eq_isSome_getElem?, contains_eq_isSome_getElem?]
  simp only [getElem?_insert]
  split <;> rename_i h
  · simp [h]
  · cases find? l x <;> simp [h]

theorem contains_insert_self (l : OrderedAssocList cmp β) (a : α) (b : β) :
    (l.insert a b).contains a = true := by
  simp [contains_insert, ReflCmp.compare_self]

end insert

section filterMapVal

variable [TransCmp cmp]

/--
Apply a function to each key-value pair,
either replacing the value or dropping it if the function returns `none`.
-/
def filterMapVal (f : α → β → Option δ) (l : OrderedAssocList cmp β) :
    OrderedAssocList cmp δ :=
  ⟨l.toAssocList.filterMapVal f, l.keysOrdered.filterMapVal⟩

@[simp] theorem toAssocList_filterMapVal (f : α → β → Option δ) (l : OrderedAssocList cmp β) :
    (filterMapVal f l).toAssocList = l.toAssocList.filterMapVal f := rfl

@[simp]
theorem getElem?_filterMapVal [LawfulEqCmp cmp] (l : OrderedAssocList cmp β) :
    (filterMapVal f l)[a]? = l[a]?.bind (fun b => f a b) :=
  AssocList.orderedFind?_filterMapVal l.keysOrdered

theorem filterMapVal_filterMapVal [LawfulEqCmp cmp]
    {f : α → γ → Option δ} {g : α → β → Option γ}
    {l : OrderedAssocList cmp β} :
    filterMapVal f (filterMapVal g l) =
      filterMapVal (fun a b => (g a b).bind (fun c => f a c)) l := by
  apply ext_toAssocList
  exact AssocList.filterMapVal_filterMapVal l.keysOrdered

end filterMapVal

section merge

variable [LawfulEqCmp cmp] [TransCmp cmp]

/--
Merge two `OrderedAssocList`s using a function `α → Option β → Option γ → Option δ`,
dropping values where the function returns `none`.
-/
def merge (f : α → Option β → Option γ → Option δ)
    (l₁ : OrderedAssocList cmp β) (l₂ : OrderedAssocList cmp γ) : OrderedAssocList cmp δ :=
  ⟨AssocList.orderedMerge cmp f l₁.toAssocList l₂.toAssocList,
    l₁.keysOrdered.orderedMerge l₂.keysOrdered⟩

@[simp] theorem toAssocList_merge {l₁ : OrderedAssocList cmp β} :
    (merge f l₁ l₂).toAssocList = AssocList.orderedMerge cmp f l₁.toAssocList l₂.toAssocList :=
  rfl

@[simp] theorem merge_nil_nil {f : α → Option β → Option γ → Option δ} :
    merge f (nil : OrderedAssocList cmp β) nil = nil := by
  apply ext_toAssocList
  simp [AssocList.orderedMerge]

@[simp] theorem merge_mk_nil_mk_cons {f : α → Option β → Option γ → Option δ} :
    merge f (⟨.nil, h⟩ : OrderedAssocList cmp β) ⟨.cons x' y' t', h'⟩ =
      filterMapVal (fun a g => f a none (some g)) ⟨.cons x' y' t', h'⟩ := by
  simp [merge, AssocList.orderedMerge]
  rfl

@[simp] theorem merge_mk_cons_mk_nil {f : α → Option β → Option γ → Option δ} :
    merge f ⟨.cons x y t, h⟩ (⟨.nil, h'⟩ : OrderedAssocList cmp γ) =
      filterMapVal (fun a b => f a (some b) none) ⟨.cons x y t, h⟩ := by
  simp [merge, AssocList.orderedMerge]
  rfl

private theorem toAssocList_merge_mk_cons_mk_cons
    (f : α → Option β → Option γ → Option δ) (x y t h x' y' t' h') :
    (merge f (⟨.cons x y t, h⟩ : OrderedAssocList cmp β) ⟨.cons x' y' t', h'⟩).toAssocList =
      match cmp x x' with
      | .lt => match f x (some y) none with
        | none => AssocList.orderedMerge cmp f t (.cons x' y' t')
        | some d => .cons x d (AssocList.orderedMerge cmp f t (.cons x' y' t'))
      | .eq => match f x (some y) (some y') with
        | none => AssocList.orderedMerge cmp f t t'
        | some d => .cons x d (AssocList.orderedMerge cmp f t t')
      | .gt => match f x' none (some y') with
        | none => AssocList.orderedMerge cmp f (.cons x y t) t'
        | some d => .cons x' d (AssocList.orderedMerge cmp f (.cons x y t) t') := by
  dsimp [merge]
  rw [AssocList.orderedMerge]
  split <;> split <;> simp_all

private theorem merge_mk_cons_mk_cons {f : α → Option β → Option γ → Option δ} :
    merge f (⟨.cons x y t, h⟩ : OrderedAssocList cmp β) ⟨.cons x' y' t', h'⟩ =
      match i: cmp x x' with
      | .lt => match w : f x (some y) none with
        | none => merge f ⟨t, h.tail⟩ ⟨.cons x' y' t', h'⟩
        | some d => ⟨.cons x d (merge f ⟨t, h.tail⟩ ⟨.cons x' y' t', h'⟩).toAssocList, by
            have p := toAssocList_merge_mk_cons_mk_cons f x y t h x' y' t' h'
            simp only [w, i] at p
            simp only [toAssocList_merge]
            simp only [← p]
            exact (merge f _ _).keysOrdered⟩
      | .eq => match w : f x (some y) (some y') with
        | none => merge f ⟨t, h.tail⟩ ⟨t', h'.tail⟩
        | some d => ⟨.cons x d (merge f ⟨t, h.tail⟩ ⟨t', h'.tail⟩).toAssocList, by
            have p := toAssocList_merge_mk_cons_mk_cons f x y t h x' y' t' h'
            simp only [w, i] at p
            simp only [toAssocList_merge]
            simp only [← p]
            exact (merge f _ _).keysOrdered⟩
      | .gt => match w : f x' none (some y') with
        | none => merge f ⟨.cons x y t, h⟩ ⟨t', h'.tail⟩
        | some d => ⟨.cons x' d (merge f ⟨.cons x y t, h⟩ ⟨t', h'.tail⟩).toAssocList, by
            have p := toAssocList_merge_mk_cons_mk_cons f x y t h x' y' t' h'
            simp only [w, i] at p
            simp only [toAssocList_merge]
            simp only [← p]
            exact (merge f _ _).keysOrdered⟩ := by grind +locals

@[simp] theorem getElem?_merge {f : α → Option β → Option γ → Option δ}
    (hf : f a none none = none) {l₁ : OrderedAssocList cmp β} {l₂} :
    (merge f l₁ l₂)[a]? = f a l₁[a]? l₂[a]? := by
  match l₁, l₂ with
  | ⟨.nil, _⟩, ⟨.nil, _⟩ => simp [getElem?, find?, AssocList.orderedMerge, hf]
  | ⟨.nil, _⟩, ⟨.cons x' y' t', h'⟩ =>
    rw [merge_mk_nil_mk_cons, getElem?_filterMapVal, getElem?_mk_nil]
    unfold Option.bind
    split <;> (rename_i w; rw [w])
    rw [hf]
  | ⟨.cons x y t, h⟩, ⟨.nil, _⟩ =>
    rw [merge_mk_cons_mk_nil, getElem?_filterMapVal, getElem?_mk_nil]
    unfold Option.bind
    split <;> (rename_i w; rw [w])
    rw [hf]
  | ⟨.cons x y t, h⟩, ⟨.cons x' y' t', h'⟩ =>
    rw [merge_mk_cons_mk_cons]
    split <;> rename_i h₁
    · split <;> rename_i h₂
      · rw [getElem?_merge hf]
        rw [getElem?_mk_cons (a := x)]
        split <;> rename_i h₃
        · rcases LawfulEqCmp.eq_of_compare h₃ with rfl
          rw [getElem?_eq_none_of_ltHeadKey, getElem?_eq_none_of_ltHeadKey, hf]
          · simp_all
          · exact h₁
          · exact h.ltHeadKey
        · rfl
      · rw [getElem?_mk_cons]
        split <;> rename_i h₃
        · rcases LawfulEqCmp.eq_of_compare h₃ with rfl
          simp only [← h₂, getElem?_mk_cons_self]
          rw [getElem?_eq_none_of_ltHeadKey]
          exact h₁
        · rw [getElem?_merge hf, getElem?_mk_cons (a := x), ite_eq_right h₃]
    · rcases (LawfulEqCmp.eq_of_compare h₁)
      split <;> rename_i h₂
      · rw [getElem?_merge hf]
        rw [getElem?_mk_cons, getElem?_mk_cons]
        split <;> rename_i h₃
        · rcases (LawfulEqCmp.eq_of_compare h₃)
          rw [getElem?_eq_none_of_ltHeadKey, getElem?_eq_none_of_ltHeadKey, hf, h₂]
          · exact h'.ltHeadKey
          · exact h.ltHeadKey
        · rfl
      · rw [getElem?_mk_cons]
        split <;> rename_i h₃
        · rcases (LawfulEqCmp.eq_of_compare h₃)
          rw [getElem?_mk_cons_self, getElem?_mk_cons_self, h₂]
        · rw [getElem?_merge hf, getElem?_mk_cons (a := x), ite_eq_right h₃,
            getElem?_mk_cons (a := x), ite_eq_right h₃]
    · split <;> rename_i h₂
      · rw [getElem?_merge hf]
        rw [getElem?_mk_cons (a := x')]
        split <;> rename_i h₃
        · rcases (LawfulEqCmp.eq_of_compare h₃)
          rw [getElem?_eq_none_of_ltHeadKey, getElem?_eq_none_of_ltHeadKey, hf]
          · exact h₂.symm
          · exact h'.ltHeadKey
          · exact OrientedCmp.lt_of_gt h₁
        · rfl
      · rw [getElem?_mk_cons]
        split <;> rename_i h₃
        · rcases (LawfulEqCmp.eq_of_compare h₃)
          simp only [getElem?_mk_cons_self]
          rw [getElem?_eq_none_of_ltHeadKey, h₂]
          exact OrientedCmp.lt_of_gt h₁
        · rw [getElem?_merge hf, getElem?_mk_cons (a := x'), ite_eq_right h₃]

theorem merge_comm
    (f : α → Option β → Option γ → Option δ) (g : α → Option γ → Option β → Option δ)
    (hg : ∀ a, g a none none = none)
    (w : ∀ a x y, f a x y = g a y x)
    (l₁ : OrderedAssocList cmp β) (l₂) : merge f l₁ l₂ = merge g l₂ l₁ := by
  ext
  simp [w, hg]

theorem merge_assoc
    (f₁ : α → Option β₁ → Option β₂ → Option γ₁) (f₂ : α → Option γ₁ → Option β₃ → Option ε)
    (g₁ : α → Option β₂ → Option β₃ → Option γ₂) (g₂ : α → Option β₁ → Option γ₂ → Option ε)
    (hf₁ : ∀ a, f₁ a none none = none) (hf₂ : ∀ a, f₂ a none none = none)
    (hg₁ : ∀ a, g₁ a none none = none) (hg₂ : ∀ a, g₂ a none none = none)
    (w : ∀ a x y z, f₂ a (f₁ a x y) z = g₂ a x (g₁ a y z))
    (l₁ : OrderedAssocList cmp β₁) (l₂) (l₃) :
    merge f₂ (merge f₁ l₁ l₂) l₃ = merge g₂ l₁ (merge g₁ l₂ l₃) := by
  ext
  simp [w, hf₁, hf₂, hg₁, hg₂]

/--
Add two `OrderedAssocList`s, taking the value from one list if the other value is missing.
(That is, treating missing values as `0`.)
-/
def add [Add β] (l₁ : OrderedAssocList cmp β) (l₂ : OrderedAssocList cmp β) :
    OrderedAssocList cmp β :=
  merge (fun _ => addOption) l₁ l₂
where
  /-- Add two values, treating missing values as `0`. -/
  addOption : Option β → Option β → Option β
    | some x, some y => some (x + y)
    | some x, none => some x
    | none, some y => some y
    | none, none => none

-- This statement will look better on a version of `OrderedAssocList` with default values,
-- where we can just write `(add l₁ l₂)[a] = l₁[a] + l₂[a]`.

@[simp] theorem getElem?_add [Add β] {l₁ : OrderedAssocList cmp β} {a : α} :
    (add l₁ l₂)[a]? =
      match l₁[a]?, l₂[a]? with
      | some x, some y => some (x + y)
      | some x, none => some x
      | none, some y => some y
      | none, none => none := by
  rw [add, getElem?_merge rfl]
  rfl

/--
Multiply two `OrderedAssocList`s,
dropping any values where the corresponding value in the other list is missing.
(That is, treating missing values as `0`.)
-/
def mul [Mul β] (l₁ : OrderedAssocList cmp β) (l₂ : OrderedAssocList cmp β) :
    OrderedAssocList cmp β :=
  merge (fun _ => mulOption) l₁ l₂
where
  /-- Multiply two values, treating missing values as `0`. -/
  mulOption : Option β → Option β → Option β
    | some x, some y => some (x * y)
    | some _, none => none
    | none, some _ => none
    | none, none => none

@[simp] theorem getElem?_mul [Mul β] {l₁ : OrderedAssocList cmp β} {a : α} :
    (mul l₁ l₂)[a]? =
      match l₁[a]?, l₂[a]? with
      | some x, some y => some (x * y)
      | some _, none => none
      | none, some _ => none
      | none, none => none := by
  rw [mul, getElem?_merge rfl]
  rfl

end merge

end OrderedAssocList
