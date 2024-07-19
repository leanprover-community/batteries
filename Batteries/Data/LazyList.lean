/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Simon Hudon
-/
import Batteries.Data.Thunk
/-!
# Lazy lists

Deprecated. This module is deprecated and will be removed in the future.
Most use cases can use `MLList`. Without custom support from the kernel
(previously provided in Lean 3) this type is not very useful,
but was ported from Lean 3 anyway.

The type `LazyList α` is a lazy list with elements of type `α`.
In the VM, these are potentially infinite lists
where all elements after the first are computed on-demand.
(This is only useful for execution in the VM,
logically we can prove that `LazyList α` is isomorphic to `List α`.)
-/

/-- Lazy list.
All elements (except the first) are computed lazily.
-/
@[deprecated "Consider using `MLList`." (since := "2024-07-15")]
inductive LazyList (α : Type u) : Type u
  /-- The empty lazy list. -/
  | nil : LazyList α
  /-- Construct a lazy list from an element and a tail inside a thunk. -/
  | cons (hd : α) (tl : Thunk <| LazyList α) : LazyList α


set_option linter.deprecated false
namespace LazyList


instance : Inhabited (LazyList α) :=
  ⟨nil⟩

/-- The singleton lazy list.  -/
def singleton : α → LazyList α
  | a => cons a <| Thunk.pure nil

/-- Constructs a lazy list from a list. -/
def ofList : List α → LazyList α
  | [] => nil
  | h :: t => cons h (ofList t)

/-- Converts a lazy list to a list.
If the lazy list is infinite,
then this function does not terminate.
-/
def toList : LazyList α → List α
  | nil => []
  | cons h t => h :: toList (t.get)

/-- Returns the first element of the lazy list,
or `default` if the lazy list is empty.
-/
def headI [Inhabited α] : LazyList α → α
  | nil => default
  | cons h _ => h

/-- Removes the first element of the lazy list.
-/
def tail : LazyList α → LazyList α
  | nil => nil
  | cons _ t => t.get

/-- Appends two lazy lists.  -/
def append : LazyList α → Thunk (LazyList α) → LazyList α
  | nil, l => l.get
  | cons h t, l => cons h (append (t.get) l)

/-- Maps a function over a lazy list. -/
def map (f : α → β) : LazyList α → LazyList β
  | nil => nil
  | cons h t => cons (f h) (map f t.get)

/-- Maps a binary function over two lazy list.
Like `LazyList.zip`, the result is only as long as the smaller input.
-/
def map₂ (f : α → β → δ) : LazyList α → LazyList β → LazyList δ
  | nil, _ => nil
  | _, nil => nil
  | cons h₁ t₁, cons h₂ t₂ => cons (f h₁ h₂) (map₂ f t₁.get t₂.get)

/-- Zips two lazy lists. -/
def zip : LazyList α → LazyList β → LazyList (α × β) :=
  map₂ Prod.mk

/-- The monadic join operation for lazy lists. -/
def join : LazyList (LazyList α) → LazyList α
  | nil => nil
  | cons h t => append h (join (t.get))

/-- The list containing the first `n` elements of a lazy list.  -/
def take : Nat → LazyList α → List α
  | 0, _ => []
  | _, nil => []
  | a + 1, cons h t => h :: take a (t.get)

/-- The lazy list of all elements satisfying the predicate.
If the lazy list is infinite and none of the elements satisfy the predicate,
then this function will not terminate.
-/
def filter (p : α → Prop) [DecidablePred p] : LazyList α → LazyList α
  | nil => nil
  | cons h t => if p h then cons h (filter p t.get) else filter p (t.get)

/-- The nth element of a lazy list as an option (like `List.get?`). -/
def get? : LazyList α → Nat → Option α
  | nil, _ => none
  | cons a _, 0 => some a
  | cons _ l, n + 1 => get? (l.get) n

/-- The infinite lazy list `[x, f x, f (f x), ...]` of iterates of a function.
This definition is partial because it creates an infinite list.
-/
partial def iterates (f : α → α) : α → LazyList α
  | x => cons x (iterates f (f x))

/-- The infinite lazy list `[i, i+1, i+2, ...]` -/
partial def iota (i : Nat) : LazyList Nat :=
  iterates Nat.succ i


instance decidableEq {α : Type u} [DecidableEq α] : DecidableEq (LazyList α)
  | nil, nil => isTrue rfl
  | cons x xs, cons y ys =>
    if h : x = y then
      match decidableEq xs.get ys.get with
      | isFalse h2 => by
        apply isFalse; simp only [cons.injEq, not_and]; intro _ xs_ys; apply h2; rw [xs_ys]
      | isTrue h2 => by apply isTrue; congr; ext; exact h2
    else by apply isFalse; simp only [cons.injEq, not_and]; intro; contradiction
  | nil, cons _ _ => by apply isFalse; simp
  | cons _ _, nil => by apply isFalse; simp

/-- Traversal of lazy lists using an applicative effect. -/
protected def traverse {m : Type u → Type u} [Applicative m] {α β : Type u} (f : α → m β) :
    LazyList α → m (LazyList β)
  | LazyList.nil => pure LazyList.nil
  | LazyList.cons x xs => LazyList.cons <$> f x <*> Thunk.pure <$> xs.get.traverse f

/-- `init xs`, if `xs` non-empty, drops the last element of the list.
Otherwise, return the empty list. -/
def init {α} : LazyList α → LazyList α
  | LazyList.nil => LazyList.nil
  | LazyList.cons x xs =>
    let xs' := xs.get
    match xs' with
    | LazyList.nil => LazyList.nil
    | LazyList.cons _ _ => LazyList.cons x (init xs')

/-- Return the first object contained in the list that satisfies
predicate `p` -/
def find {α} (p : α → Prop) [DecidablePred p] : LazyList α → Option α
  | nil => none
  | cons h t => if p h then some h else t.get.find p

/-- `interleave xs ys` creates a list where elements of `xs` and `ys` alternate. -/
def interleave {α} : LazyList α → LazyList α → LazyList α
  | LazyList.nil, xs => xs
  | a@(LazyList.cons _ _), LazyList.nil => a
  | LazyList.cons x xs, LazyList.cons y ys =>
    LazyList.cons x (LazyList.cons y (interleave xs.get ys.get))

/-- `interleaveAll (xs::ys::zs::xss)` creates a list where elements of `xs`, `ys`
and `zs` and the rest alternate. Every other element of the resulting list is taken from
`xs`, every fourth is taken from `ys`, every eighth is taken from `zs` and so on. -/
def interleaveAll {α} : List (LazyList α) → LazyList α
  | [] => LazyList.nil
  | x :: xs => interleave x (interleaveAll xs)

/-- Monadic bind operation for `LazyList`. -/
protected def bind {α β} : LazyList α → (α → LazyList β) → LazyList β
  | LazyList.nil, _ => LazyList.nil
  | LazyList.cons x xs, f => (f x).append (xs.get.bind f)

/-- Reverse the order of a `LazyList`.
It is done by converting to a `List` first because reversal involves evaluating all
the list and if the list is all evaluated, `List` is a better representation for
it than a series of thunks. -/
def reverse {α} (xs : LazyList α) : LazyList α :=
  ofList xs.toList.reverse

instance : Monad LazyList where
  pure := @LazyList.singleton
  bind := @LazyList.bind

-- Porting note: Added `Thunk.pure` to definition.
theorem append_nil {α} (xs : LazyList α) : xs.append (Thunk.pure LazyList.nil) = xs := by
  induction xs using LazyList.rec with
  | nil => simp only [Thunk.pure, append, Thunk.get]
  | cons _ _ => simpa only [append, cons.injEq, true_and]
  | mk _ ih => ext; apply ih

theorem append_assoc {α} (xs ys zs : LazyList α) :
    (xs.append ys).append zs = xs.append (ys.append zs) := by
  induction xs using LazyList.rec with
  | nil => simp only [append, Thunk.get]
  | cons _ _ => simpa only [append, cons.injEq, true_and]
  | mk _ ih => ext; apply ih

-- Porting note: Rewrote proof of `append_bind`.
theorem append_bind {α β} (xs : LazyList α) (ys : Thunk (LazyList α)) (f : α → LazyList β) :
    (xs.append ys).bind f = (xs.bind f).append (ys.get.bind f) := by
  match xs with
  | LazyList.nil =>
    simp only [append, Thunk.get, LazyList.bind]
  | LazyList.cons x xs =>
    simp only [append, Thunk.get, LazyList.bind]
    have := append_bind xs.get ys f
    simp only [Thunk.get] at this
    rw [this, append_assoc]

-- TODO: upstream from mathlib
-- instance : LawfulMonad LazyList.{u}

/-- Try applying function `f` to every element of a `LazyList` and
return the result of the first attempt that succeeds. -/
def mfirst {m} [Alternative m] {α β} (f : α → m β) : LazyList α → m β
  | nil => failure
  | cons x xs => f x <|> xs.get.mfirst f

/-- Membership in lazy lists -/
protected def Mem {α} (x : α) : LazyList α → Prop
  | nil => False
  | cons y ys => x = y ∨ ys.get.Mem x

instance {α} : Membership α (LazyList α) :=
  ⟨LazyList.Mem⟩

instance Mem.decidable {α} [DecidableEq α] (x : α) : ∀ xs : LazyList α, Decidable (x ∈ xs)
  | LazyList.nil => by
    apply Decidable.isFalse
    simp [Membership.mem, LazyList.Mem]
  | LazyList.cons y ys =>
    if h : x = y then by
      apply Decidable.isTrue
      simp only [Membership.mem, LazyList.Mem]
      exact Or.inl h
    else by
      have := Mem.decidable x ys.get
      have : (x ∈ ys.get) ↔ (x ∈ cons y ys) := by simp [(· ∈ ·), LazyList.Mem, h]
      exact decidable_of_decidable_of_iff this

@[simp]
theorem mem_nil {α} (x : α) : x ∈ @LazyList.nil α ↔ False := by
  simp [Membership.mem, LazyList.Mem]

@[simp]
theorem mem_cons {α} (x y : α) (ys : Thunk (LazyList α)) :
    x ∈ @LazyList.cons α y ys ↔ x = y ∨ x ∈ ys.get := by
  simp [Membership.mem, LazyList.Mem]

theorem forall_mem_cons {α} {p : α → Prop} {a : α} {l : Thunk (LazyList α)} :
    (∀ x ∈ @LazyList.cons _ a l, p x) ↔ p a ∧ ∀ x ∈ l.get, p x := by
  simp only [Membership.mem, LazyList.Mem, or_imp, forall_and, forall_eq]

/-! ### map for partial functions -/


/-- Partial map. If `f : ∀ a, p a → β` is a partial function defined on
  `a : α` satisfying `p`, then `pmap f l h` is essentially the same as `map f l`
  but is defined only when all members of `l` satisfy `p`, using the proof
  to apply `f`. -/
@[simp]
def pmap {α β} {p : α → Prop} (f : ∀ a, p a → β) : ∀ l : LazyList α, (∀ a ∈ l, p a) → LazyList β
  | LazyList.nil, _ => LazyList.nil
  | LazyList.cons x xs, H =>
    LazyList.cons (f x (forall_mem_cons.1 H).1) (xs.get.pmap f (forall_mem_cons.1 H).2)

/-- "Attach" the proof that the elements of `l` are in `l` to produce a new `LazyList`
  with the same elements but in the type `{x // x ∈ l}`. -/
def attach {α} (l : LazyList α) : LazyList { x // x ∈ l } :=
  pmap Subtype.mk l fun _ => id

instance {α} [Repr α] : Repr (LazyList α) :=
  ⟨fun xs _ => repr xs.toList⟩

end LazyList
