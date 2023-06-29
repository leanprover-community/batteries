/-
Copyright (c) 2018 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Keeley Hoek, Simon Hudon, Scott Morrison
-/

/-! # Monadic lazy lists.

Lazy lists with "laziness" controlled by an arbitrary monad.
-/


/-!
In an initial section we describe the specification of `ListM`,
and provide a private unsafe implementation,
and then a public `opaque` wrapper of this implementation, satisfying the specification.
-/
namespace ListM

private structure Spec (m : Type u → Type u) where
  listM : Type u → Type u
  nil : listM α
  cons : α → listM α → listM α
  thunk : (Unit → listM α) → listM α
  squash : (Unit → m (listM α)) → listM α
  uncons : [Monad m] → listM α → m (Option (α × listM α))

instance : Nonempty (Spec m) := .intro
  { listM := fun _ => PUnit
    nil := ⟨⟩
    cons := fun _ _ => ⟨⟩
    thunk := fun _ => ⟨⟩
    squash := fun _ => ⟨⟩
    uncons := fun _ => pure none }

private unsafe inductive ListMImpl (m : Type u → Type u) (α : Type u) : Type u
  | nil : ListMImpl m α
  | cons : α → ListMImpl m α → ListMImpl m α
  | thunk : Thunk (ListMImpl m α) → ListMImpl m α
  | squash : (Unit → m (ListMImpl m α)) → ListMImpl m α

private unsafe def unconsImpl {m : Type u → Type u} [Monad m] :
    ListMImpl m α → m (Option (α × ListMImpl m α))
  | .nil => pure none
  | .thunk t => unconsImpl t.get
  | .squash t => t () >>= unconsImpl
  | .cons x xs => return (x, xs)

@[inline] private unsafe def specImpl (m) : Spec m where
  listM := ListMImpl m
  nil := .nil
  cons := .cons
  thunk f := .thunk (.mk f)
  squash := .squash
  uncons := unconsImpl

@[implemented_by specImpl]
private opaque spec (m) : ListM.Spec m

end ListM

/-- A monadic lazy list, controlled by an arbitrary monad. -/
def ListM (m : Type u → Type u) (α : Type u) : Type u := (ListM.spec m).listM α

namespace ListM

/-- The empty `ListM`. -/
@[inline] def nil : ListM m α := (ListM.spec m).nil

/--
Constructs a `ListM` from head and tail.
-/
@[inline] def cons : α → ListM m α → ListM m α := (ListM.spec m).cons

/-- Embed a non-monadic thunk as a lazy list. -/
@[inline] def thunk : (Unit → ListM m α) → ListM m α := (ListM.spec m).thunk

/-- Lift a monadic lazy list inside the monad to a monadic lazy list. -/
def squash : (Unit → m (ListM m α)) → ListM m α := (ListM.spec m).squash

/-- Deconstruct a `ListM`, returning inside the monad an optional pair `α × ListM m α`
representing the head and tail of the list. -/
@[inline] def uncons [Monad m] : ListM.{u} m α → m (Option (α × ListM m α)) := (ListM.spec m).uncons

instance : EmptyCollection (ListM m α) := ⟨nil⟩
instance : Inhabited (ListM m α) := ⟨nil⟩

private local instance [Monad n] : Inhabited (δ → (α → δ → n (ForInStep δ)) → n δ) where
  default d _ := pure d in
/-- The implementation of `ForIn`, which enables `for a in L do ...` notation. -/
@[specialize] protected partial def forIn [Monad m] [Monad n] [MonadLiftT m n]
    (as : ListM m α) (init : δ) (f : α → δ → n (ForInStep δ)) : n δ := do
  match ← (as.uncons :) with
  | none => pure init
  | some (a, t) => match (← f a init) with
      | ForInStep.done d  => pure d
      | ForInStep.yield d => t.forIn d f

instance [Monad m] [MonadLiftT m n] : ForIn n (ListM m α) α where
  forIn := ListM.forIn

/-- Construct a `ListM` recursively. Failures from `f` will result in `uncons` failing.  -/
partial def fix [Monad m] (f : α → m α) (x : α) : ListM m α :=
  cons x <| squash fun _ => fix f <$> f x

/-- Construct a `ListM` recursively. If `f` returns `none` the list will terminate. -/
partial def fix? [Monad m] (f : α → m (Option α)) (x : α) : ListM m α :=
  cons x <| squash fun _ => do
    match ← f x with
    | none => return nil
    | some x' => return fix? f x'

/-- Construct a `ListM` by iteration. (`m` must be a stateful monad for this to be useful.) -/
partial def iterate [Monad m] (f : m α) : ListM m α :=
  squash fun _ => return cons (← f) (iterate f)

/-- Repeatedly apply a function `f : α → m (α × List β)` to an initial `a : α`,
accumulating the elements of the resulting `List β` as a single monadic lazy list.

(This variant allows starting with a specified `List β` of elements, as well. )-/
partial def fixlWith [Monad m] {α β : Type u} (f : α → m (α × List β))
    (s : α) (l : List β) : ListM m β :=
  thunk fun _ =>
    match l with
    | b :: rest => cons b (fixlWith f s rest)
    | [] => squash fun _ => do
      let (s', l) ← f s
      match l with
      | b :: rest => pure <| cons b (fixlWith f s' rest)
      | [] => pure <| fixlWith f s' []

/-- Repeatedly apply a function `f : α → m (α × List β)` to an initial `a : α`,
accumulating the elements of the resulting `List β` as a single monadic lazy list. -/
def fixl [Monad m] {α β : Type u} (f : α → m (α × List β)) (s : α) : ListM m β :=
  fixlWith f s []

/-- Compute, inside the monad, whether a `ListM` is empty. -/
def isEmpty [Monad m] (xs : ListM m α) : m (ULift Bool) :=
  (ULift.up ∘ Option.isSome) <$> uncons xs

/-- Convert a `List` to a `ListM`. -/
def ofList : List α → ListM m α
  | [] => nil
  | h :: t => cons h (thunk fun _ => ofList t)

/-- Convert a `List` of values inside the monad into a `ListM`. -/
def ofListM [Monad m] : List (m α) → ListM m α
  | [] => nil
  | h :: t => squash fun _ => return cons (← h) (ofListM t)

/-- Extract a list inside the monad from a `ListM`. -/
partial def force [Monad m] (L : ListM m α) : m (List α) := do
  match ← L.uncons with
  | none => pure []
  | some (x, xs) => return x :: (← xs.force)

/-- Extract an array inside the monad from a `ListM`. -/
def asArray [Monad m] (L : ListM m α) : m (Array α) := do
  let mut r := #[]
  for a in L do
    r := r.push a
  return r

/-- Performs a monadic case distinction on a `ListM` when the motive is a `ListM` as well. -/
@[specialize]
def casesM [Monad m] (xs : ListM m α)
    (hnil : Unit → m (ListM m β)) (hcons : α → ListM m α → m (ListM m β)) : ListM m β :=
  squash fun _ => do
    match ← xs.uncons with
    | none => hnil ()
    | some (x, xs) => hcons x xs

/--
Performs a case distinction on a `ListM` when the motive is a `ListM` as well.
(We need to be in a monadic context to distinguish a nil from a cons.)
-/
@[specialize]
def cases [Monad m] (xs : ListM m α)
    (hnil : Unit → ListM m β) (hcons : α → ListM m α → ListM m β) : ListM m β :=
  xs.casesM (fun _ => return hnil ()) (fun x xs => return hcons x xs)

/-- Gives the monadic lazy list consisting all of folds of a function on a given initial element.
Thus `[a₀, a₁, ...].foldsM f b` will give `[b, ← f b a₀, ← f (← f b a₀) a₁, ...]`. -/
partial def foldsM [Monad m] (f : β → α → m β) (init : β) (L : ListM m α) : ListM m β :=
  cons init <| squash fun _ => do
    match ← L.uncons with
    | none => return nil
    | some (x, xs) => return foldsM f (← f init x) xs

/-- Gives the monadic lazy list consisting all of folds of a function on a given initial element.
Thus `[a₀, a₁, ...].foldsM f b` will give `[b, f b a₀, f (f b a₀) a₁, ...]`. -/
def folds [Monad m] (f : β → α → β) (init : β) (L : ListM m α) : ListM m β :=
  L.foldsM (fun b a => pure (f b a)) init

/-- Take the first `n` elements, as a list inside the monad. -/
partial def takeAsList [Monad m] (xs : ListM m α) (n : Nat) : m (List α) :=
  go n [] xs
where
  /-- Implementation of `ListM.takeAsList`. -/
  go (r : Nat) (acc : List α) (xs : ListM m α) : m (List α) :=
    match r with
    | 0 => pure acc.reverse
    | r+1 => do match ← xs.uncons with
      | none => pure acc.reverse
      | some (x, xs) => go r (x :: acc) xs

/-- Take the first `n` elements, as an array inside the monad. -/
partial def takeAsArray [Monad m] (xs : ListM m α) (n : Nat) : m (Array α) :=
  go n #[] xs
where
  /-- Implementation of `ListM.takeAsArray`. -/
  go (r : Nat) (acc : Array α) (xs : ListM m α) : m (Array α) :=
    match r with
    | 0 => pure acc
    | r+1 => do match ← xs.uncons with
      | none => pure acc
      | some (x, xs) => go r (acc.push x) xs

/-- Take the first `n` elements. -/
partial def take [Monad m] (xs : ListM m α) : Nat → ListM m α
  | 0 => nil
  | n+1 => xs.cases (fun _ => nil) fun h l => cons h (l.take n)

/-- Drop the first `n` elements. -/
def drop [Monad m] (xs : ListM m α) : Nat → ListM m α
  | 0 => xs
  | n+1 => xs.cases (fun _ => nil) fun _ l => l.drop n

/-- Apply a function which returns values in the monad to every element of a `ListM`. -/
partial def mapM [Monad m] (f : α → m β) (xs : ListM m α) : ListM m β :=
  xs.cases (fun _ => nil) fun x xs => squash fun _ => return cons (← f x) (xs.mapM f)

/-- Apply a function to every element of a `ListM`. -/
def map [Monad m] (f : α → β) (L : ListM m α) : ListM m β :=
  L.mapM fun a => pure (f a)

/-- Filter a `ListM` using a monadic function. -/
partial def filterM [Monad m] (p : α → m (ULift Bool)) (L : ListM m α) : ListM m α :=
  L.casesM (fun _ => pure nil) fun x xs =>
    return if (← p x).down then cons x (filterM p xs) else filterM p xs

/-- Filter a `ListM`. -/
def filter [Monad m] (p : α → Bool) (L : ListM m α) : ListM m α :=
  L.filterM fun a => pure <| .up (p a)

/-- Filter and transform a `ListM` using a function that returns values inside the monad. -/
-- Note that the type signature has changed since Lean 3, when we allowed `f` to fail.
-- Use `try?` from `Mathlib.Control.Basic` to lift a possibly failing function to `Option`.
partial def filterMapM [Monad m] (f : α → m (Option β)) (xs : ListM m α) : ListM m β :=
  xs.casesM (fun _ => pure nil) fun x xs => do
    match ← f x with
    | none => return xs.filterMapM f
    | some a => return cons a (xs.filterMapM f)

/-- Filter and transform a `ListM` using an `Option` valued function. -/
def filterMap [Monad m] (f : α → Option β) : ListM m α → ListM m β :=
  filterMapM fun a => do pure (f a)

/-- Take the initial segment of the lazy list, until the function `f` first returns `false`. -/
partial def takeWhileM [Monad m] (f : α → m (ULift Bool)) (L : ListM m α) : ListM m α :=
  L.casesM (fun _ => pure nil) fun x xs =>
    return if !(← f x).down then nil else cons x (xs.takeWhileM f)

/-- Take the initial segment of the lazy list, until the function `f` first returns `false`. -/
def takeWhile [Monad m] (f : α → Bool) : ListM m α → ListM m α :=
  takeWhileM fun a => pure (.up (f a))

/-- Concatenate two monadic lazy lists. -/
partial def append [Monad m] (xs : ListM m α) (ys : Unit → ListM m α) : ListM m α :=
  xs.cases ys fun x xs => cons x (append xs ys)

/-- Join a monadic lazy list of monadic lazy lists into a single monadic lazy list. -/
partial def join [Monad m] (xs : ListM m (ListM m α)) : ListM m α :=
  xs.cases (fun _ => nil) fun x xs => append x (fun _ => join xs)

/-- Enumerate the elements of a monadic lazy list, starting at a specified offset. -/
partial def enumFrom [Monad m] (n : Nat) (xs : ListM m α) : ListM m (Nat × α) :=
  xs.cases (fun _ => nil) fun x xs => cons (n, x) (xs.enumFrom (n+1))

/-- Enumerate the elements of a monadic lazy list. -/
def enum [Monad m] : ListM m α → ListM m (Nat × α) := enumFrom 0

/-- The infinite monadic lazy list of natural numbers.-/
def range [Monad m] : ListM m Nat := ListM.fix (fun n => pure (n + 1)) 0

/-- Iterate through the elements of `Fin n`. -/
partial def fin (n : Nat) : ListM m (Fin n) := go 0 where
  /-- Implementation of `ListM.fin`. -/
  go (i : Nat) : ListM m (Fin n) :=
    if h : i < n then cons ⟨i, h⟩ (thunk fun _ => go (i+1)) else nil

/-- Convert an array to a monadic lazy list. -/
partial def ofArray {α : Type} (L : Array α) : ListM m α := go 0 where
  /-- Implementation of `ListM.ofArray`. -/
  go (i : Nat) : ListM m α :=
    if h : i < L.size then cons (L.get ⟨i, h⟩) (thunk fun _ => go (i+1)) else nil

/-- Group the elements of a lazy list into chunks of a given size.
If the lazy list is finite, the last chunk may be smaller (possibly even length 0). -/
partial def chunk [Monad m] (L : ListM m α) (n : Nat) : ListM m (Array α) := go n #[] L where
  /-- Implementation of `ListM.chunk`. -/
  go (r : Nat) (acc : Array α) (M : ListM m α) : ListM m (Array α) :=
    match r with
    | 0 => cons acc (thunk fun _ => go n #[] M)
    | r+1 => squash fun _ => do
      match ← M.uncons with
      | none => return cons acc nil
      | some (a, M') => return go r (acc.push a) M'

/-- Add one element to the end of a monadic lazy list. -/
def concat [Monad m] (L : ListM m α) (a : α) : ListM m α := L.append (fun _ => cons a nil)

/-- Take the product of two monadic lazy lists. -/
partial def zip [Monad m] (L : ListM m α) (M : ListM m β) : ListM.{u} m (α × β) :=
  L.cases (fun _ => nil) fun a L =>
  M.cases (fun _ => nil) fun b M =>
  cons (a, b) (L.zip M)

/-- Apply a function returning a monadic lazy list to each element of a monadic lazy list,
joining the results. -/
partial def bind [Monad m] (xs : ListM m α) (f : α → ListM m β) : ListM m β :=
  xs.cases (fun _ => nil) fun x xs => append (f x) (fun _ => bind xs f)

/-- Convert any value in the monad to the singleton monadic lazy list. -/
def monadLift [Monad m] (x : m α) : ListM m α :=
  squash fun _ => return cons (← x) nil

/-- Lift the monad of a lazy list. -/
partial def liftM [Monad m] [Monad n] [MonadLiftT m n] (L : ListM m α) : ListM n α :=
  squash fun _ =>
    return match ← (uncons L : m _) with
    | none => nil
    | some (a, L') => cons a L'.liftM

/-- Given a lazy list in a state monad, run it on some initial state, recording the states. -/
partial def runState [Monad m] (L : ListM (StateT.{u} σ m) α) (s : σ) : ListM m (α × σ) :=
  squash fun _ =>
    return match ← (uncons L).run s with
    | (none, _) => nil
    | (some (a, L'), s') => cons (a, s') (L'.runState s')

/-- Given a lazy list in a state monad, run it on some initial state. -/
def runState' [Monad m] (L : ListM (StateT.{u} σ m) α) (s : σ) : ListM m α :=
  L.runState s |>.map (·.1)

/-- Return the head of a monadic lazy list if it exists, as an `Option` in the monad. -/
def head? [Monad m] (L : ListM m α) : m (Option α) := return (← L.uncons).map (·.1)

/-- Take the initial segment of the lazy list,
up to and including the first place where `f` gives `true`. -/
partial def takeUpToFirstM [Monad m] (L : ListM m α) (f : α → m (ULift Bool)) : ListM m α :=
  L.casesM (fun _ => pure nil) fun x xs =>
    return cons x <| if (← (f x)).down then nil else xs.takeUpToFirstM f

/-- Take the initial segment of the lazy list,
up to and including the first place where `f` gives `true`. -/
def takeUpToFirst [Monad m] (L : ListM m α) (f : α → Bool) : ListM m α :=
  L.takeUpToFirstM fun a => pure (.up (f a))

/-- Gets the last element of a monadic lazy list, as an option in the monad.
This will run forever if the list is infinite. -/
partial def getLast? [Monad m] (L : ListM m α) : m (Option α) := do
  match ← uncons L with
  | none => return none
  | some (x, xs) => aux x xs
where
  /-- Implementation of `ListM.aux`. -/
  aux (x : α) (L : ListM m α) : m (Option α) := do
    match ← uncons L with
    | none => return some x
    | some (y, ys) => aux y ys

/-- Gets the last element of a monadic lazy list, or the default value if the list is empty.
This will run forever if the list is infinite. -/
partial def getLast! [Monad m] [Inhabited α] (L : ListM m α) : m α := Option.get! <$> L.getLast?

/-- Folds a binary function across a monadic lazy list, from an initial starting value.
This will run forever if the list is infinite. -/
partial def foldM [Monad m] (f : β → α → m β) (init : β) (L : ListM m α) : m β :=
  return (← L.foldsM f init |>.getLast?).getD init -- `foldsM` is always non-empty, anyway.

/-- Folds a binary function across a monadic lazy list, from an initial starting value.
This will run forever if the list is infinite. -/
partial def fold [Monad m] (f : β → α → β) (init : β) (L : ListM m α) : m β :=
  L.foldM (fun b a => pure (f b a)) init

/--
Return the head of a monadic lazy list, as a value in the monad.
Fails if the list is empty.
-/
def head [Monad m] [Alternative m] (L : ListM m α) : m α := do
  let some (r, _) ← L.uncons | failure
  return r

/--
Apply a function returning values inside the monad to a monadic lazy list,
returning only the first successful result.
-/
def firstM [Monad m] [Alternative m] (L : ListM m α) (f : α → m (Option β)) : m β :=
  (L.filterMapM f).head

/-- Return the first value on which a predicate returns true. -/
def first [Monad m] [Alternative m] (L : ListM m α) (p : α → Bool) : m α := (L.filter p).head

instance [Monad m] : Monad (ListM m) where
  pure a := cons a nil
  map := map
  bind := bind

instance [Monad m] : Alternative (ListM m) where
  failure := nil
  orElse := ListM.append

instance [Monad m] : MonadLift m (ListM m) where
  monadLift := monadLift
