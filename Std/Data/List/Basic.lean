/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Std.Classes.SetNotation
import Std.Tactic.NoMatch

open Decidable List

variable {α : Type u} {β : Type v} {γ : Type w}

namespace List

/--
`l₁ ⊆ l₂` means that every element of `l₁` is also an element of `l₂`, ignoring multiplicity.
-/
protected def Subset (l₁ l₂ : List α) := ∀ ⦃a : α⦄, a ∈ l₁ → a ∈ l₂

instance : Subset (List α) := ⟨List.Subset⟩

instance decidableBEx (p : α → Prop) [DecidablePred p] : ∀ l : List α, Decidable (∃ x ∈ l, p x)
  | [] => isFalse fun.
  | x :: xs =>
    if h₁ : p x then isTrue ⟨x, .head .., h₁⟩ else
      match decidableBEx p xs with
      | isTrue h₂ => isTrue <| let ⟨y, hm, hp⟩ := h₂; ⟨y, .tail _ hm, hp⟩
      | isFalse h₂ => isFalse fun
        | ⟨y, .tail _ h, hp⟩ => h₂ ⟨y, h, hp⟩
        | ⟨_, .head .., hp⟩ => h₁ hp

instance decidableBAll (p : α → Prop) [DecidablePred p] (l : List α) : Decidable (∀ x ∈ l, p x) :=
  if h : ∃ x ∈ l, ¬p x then isFalse <| let ⟨x, h, np⟩ := h; fun al => np (al x h)
  else isTrue <| fun x hx => if h' : p x then h' else (h ⟨x, hx, h'⟩).elim

/--
Computes the "bag intersection" of `l₁` and `l₂`, that is,
the collection of elements of `l₁` which are also in `l₂`. As each element
is identified, it is removed from `l₂`, so elements are counted with multiplicity.
-/
protected def bagInter {α} [BEq α] : List α → List α → List α
  | [], _ => []
  | _, [] => []
  | a :: l₁, l₂ => if l₂.elem a then a :: List.bagInter l₁ (l₂.erase a) else List.bagInter l₁ l₂

/-- Computes the difference of `l₁` and `l₂`, by removing each element in `l₂` from `l₁`. -/
protected def diff {α} [BEq α] : List α → List α → List α
  | l, [] => l
  | l₁, a :: l₂ => if l₁.elem a then List.diff (l₁.erase a) l₂ else List.diff l₁ l₂

open Option Nat

/-- Get the tail of a nonempty list, or return `[]` for `[]`. -/
def tail : List α → List α
  | []    => []
  | _::as => as

/--
Given a function `f : Nat → α → β` and `as : list α`, `as = [a₀, a₁, ...]`, returns the list
`[f 0 a₀, f 1 a₁, ...]`.
-/
def mapIdx (f : Nat → α → β) (as : List α) : List β := go 0 as where
  /-- Auxiliary for `mapIdx` that calculates `go k [a₀, a₁, ...] = [f k a₀, f (k + 1) a₁, ...]` -/
  go : Nat → List α → List β
  | _, [] => []
  | k, a :: as => f k a :: go (k+1) as

/-- Applicative variant of `mapIdx`. -/
def mapIdxM {m : Type v → Type w} [Applicative m]
    (as : List α) (f : Nat → α → m β) : m (List β) := go 0 as where
  /-- Auxiliary for `mapIdxM` -/
  go : Nat → List α → m (List β)
  | _,  [] => pure []
  | n, a :: as => List.cons <$> f n a <*> go (n + 1) as

/--
`after p xs` is the suffix of `xs` after the first element that satisfies
`p`, not including that element.
```lean
after      (eq 1)       [0, 1, 2, 3] = [2, 3]
drop_while (not ∘ eq 1) [0, 1, 2, 3] = [1, 2, 3]
```
-/
def after (p : α → Prop) [DecidablePred p] : List α → List α
  | [] => []
  | x :: xs => if p x then xs else after p xs

/-- Returns the index of the first element satisfying `p`, or the length of the list otherwise. -/
def findIdx (p : α → Prop) [DecidablePred p] : List α → Nat
  | [] => 0
  | a :: l => if p a then 0 else succ (findIdx p l)

/-- Returns the index of the first element equal to `a`, or the length of the list otherwise. -/
def indexOf [BEq α] (a : α) : List α → Nat := findIdx (a == ·)

/-- Returns the index of the first element equal to `a`, or the length of the list otherwise. -/
@[simp] def removeNth : List α → Nat → List α
  | [], _ => []
  | _ :: xs, 0 => xs
  | x :: xs, i+1 => x :: removeNth xs i

/-- Calculates the OR of a list of bools. -/
def bor (l : List Bool) : Bool := any l id

/-- Calculates the AND of a list of bools. -/
def band (l : List Bool) : Bool := all l id

/-- Inserts an element into a list without duplication. -/
protected def insert [DecidableEq α] (a : α) (l : List α) : List α :=
  if a ∈ l then l else a :: l

/--
Constructs the union of two lists, by inserting the elements of `l₁` in reverse order to `l₂`.
As a result, `l₂` will always be a suffix, but only the last occurrence of each element in `l₁`
will be retained (but order will otherwise be preserved).
-/
protected def union [DecidableEq α] (l₁ l₂ : List α) : List α :=
  foldr .insert l₂ l₁

instance [DecidableEq α] : Union (List α) :=
  ⟨List.union⟩

/--
Constructs the intersection of two lists, by filtering the elements of `l₁` that are in `l₂`.
Unlike `bagInter` this does not preserve multiplicity: `[1, 1].inter [1]` is `[1, 1]`.
-/
protected def inter [DecidableEq α] (l₁ l₂ : List α) : List α :=
  filter (· ∈ l₂) l₁

instance [DecidableEq α] : Inter (List α) := ⟨List.inter⟩

/-- Get the last element of a list, or panic on the empty list. -/
def last! [Inhabited α] : List α → α
  | [] => panic! "empty list"
  | [a] => a
  | [_, b] => b
  | _ :: _ :: l => last! l

/--
`l₁ <+ l₂`, or `Sublist l₁ l₂`, says that `l₁` is a (non-contiguous) subsequence of `l₂`.
-/
inductive Sublist {α} : List α → List α → Prop
  | /-- the base case: `[]` is a sublist of `[]` -/
    slnil : Sublist [] []
  | /-- If `l₁` is a subsequence of `l₂`, then it is also a subsequence of `a :: l₂`. -/
    cons a : Sublist l₁ l₂ → Sublist l₁ (a :: l₂)
  | /-- If `l₁` is a subsequence of `l₂`, then `a :: l₁` is a subsequence of `a :: l₂`. -/
    cons2 a : Sublist l₁ l₂ → Sublist (a :: l₁) (a :: l₂)

@[inheritDoc] scoped infixl:50 " <+ " => Sublist
