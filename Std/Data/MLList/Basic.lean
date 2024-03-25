/-
Copyright (c) 2018 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Keeley Hoek, Simon Hudon, Scott Morrison
-/

/-! # Monadic lazy lists.

Lazy lists with "laziness" controlled by an arbitrary monad.
-/


/-!
In an initial section we describe the specification of `MLList`,
and provide a private unsafe implementation,
and then a public `opaque` wrapper of this implementation, satisfying the specification.
-/
namespace MLList

private structure Spec (m : Type u → Type u) where
  listM : Type u → Type u
  nil : listM α
  cons : α → listM α → listM α
  thunk : (Unit → listM α) → listM α
  squash : (Unit → m (listM α)) → listM α
  uncons : [Monad m] → listM α → m (Option (α × listM α))
  uncons? : listM α → Option (Option (α × listM α))

instance : Nonempty (Spec m) := .intro
  { listM := fun _ => PUnit
    nil := ⟨⟩
    cons := fun _ _ => ⟨⟩
    thunk := fun _ => ⟨⟩
    squash := fun _ => ⟨⟩
    uncons := fun _ => pure none
    uncons? := fun _ => none }

private unsafe inductive MLListImpl (m : Type u → Type u) (α : Type u) : Type u
  | nil : MLListImpl m α
  | cons : α → MLListImpl m α → MLListImpl m α
  | thunk : Thunk (MLListImpl m α) → MLListImpl m α
  | squash : (Unit → m (MLListImpl m α)) → MLListImpl m α

private unsafe def unconsImpl {m : Type u → Type u} [Monad m] :
    MLListImpl m α → m (Option (α × MLListImpl m α))
  | .nil => pure none
  | .thunk t => unconsImpl t.get
  | .squash t => t () >>= unconsImpl
  | .cons x xs => return (x, xs)

private unsafe def uncons?Impl : MLListImpl m α → Option (Option (α × MLListImpl m α))
  | .nil => pure none
  | .cons x xs => pure (x, xs)
  | _ => none

@[inline] private unsafe def specImpl (m) : Spec m where
  listM := MLListImpl m
  nil := .nil
  cons := .cons
  thunk f := .thunk (.mk f)
  squash := .squash
  uncons := unconsImpl
  uncons? := uncons?Impl

@[implemented_by specImpl]
private opaque spec (m) : MLList.Spec m

end MLList

/-- A monadic lazy list, controlled by an arbitrary monad. -/
def MLList (m : Type u → Type u) (α : Type u) : Type u := (MLList.spec m).listM α

namespace MLList

/-- The empty `MLList`. -/
@[inline] def nil : MLList m α := (MLList.spec m).nil

/--
Constructs a `MLList` from head and tail.
-/
@[inline] def cons : α → MLList m α → MLList m α := (MLList.spec m).cons

/-- Embed a non-monadic thunk as a lazy list. -/
@[inline] def thunk : (Unit → MLList m α) → MLList m α := (MLList.spec m).thunk

/-- Lift a monadic lazy list inside the monad to a monadic lazy list. -/
def squash : (Unit → m (MLList m α)) → MLList m α := (MLList.spec m).squash

/-- Deconstruct a `MLList`, returning inside the monad an optional pair `α × MLList m α`
representing the head and tail of the list. -/
@[inline] def uncons [Monad m] : MLList.{u} m α → m (Option (α × MLList m α)) :=
  (MLList.spec m).uncons

/-- Try to deconstruct a `MLList`, returning an optional pair `α × MLList m α`
representing the head and tail of the list if it is already evaluated, and `none` otherwise. -/
@[inline] def uncons? : MLList.{u} m α → Option (Option (α × MLList m α)) :=
  (MLList.spec m).uncons?

instance : EmptyCollection (MLList m α) := ⟨nil⟩
instance : Inhabited (MLList m α) := ⟨nil⟩

private local instance [Monad n] : Inhabited (δ → (α → δ → n (ForInStep δ)) → n δ) where
  default d _ := pure d in
/-- The implementation of `ForIn`, which enables `for a in L do ...` notation. -/
@[specialize] protected partial def forIn [Monad m] [Monad n] [MonadLiftT m n]
    (as : MLList m α) (init : δ) (f : α → δ → n (ForInStep δ)) : n δ := do
  match ← as.uncons with
  | none => pure init
  | some (a, t) => match (← f a init) with
      | ForInStep.done d  => pure d
      | ForInStep.yield d => t.forIn d f

instance [Monad m] [MonadLiftT m n] : ForIn n (MLList m α) α where
  forIn := MLList.forIn

/-- Construct a singleton monadic lazy list from a single monadic value. -/
def singletonM [Monad m] (x : m α) : MLList m α :=
  .squash fun _ => do return .cons (← x) .nil

/-- Construct a singleton monadic lazy list from a single value. -/
def singleton [Monad m] (x : α) : MLList m α :=
  .singletonM (pure x)

/-- Construct a `MLList` recursively. Failures from `f` will result in `uncons` failing.  -/
partial def fix [Monad m] (f : α → m α) (x : α) : MLList m α :=
  cons x <| squash fun _ => fix f <$> f x

/--
Constructs an `MLList` recursively, with state in `α`, recording terms from `β`.
If `f` returns `none` the list will terminate.

Variant of `MLList.fix?` that allows returning values of a different type.
-/
partial def fix?' [Monad m] (f : α → m (Option (β × α))) (init : α) : MLList m β :=
  squash fun _ => do
    match ← f init with
    | none => pure .nil
    | some (b, a) => pure (.cons b (fix?' f a))

/--
Constructs an `MLList` recursively. If `f` returns `none` the list will terminate.

Returns the initial value as the first element.
-/
partial def fix? [Monad m] (f : α → m (Option α)) (x : α) : MLList m α :=
  cons x <| squash fun _ => do
    match ← f x with
    | none => return nil
    | some x' => return fix? f x'

/-- Construct a `MLList` by iteration. (`m` must be a stateful monad for this to be useful.) -/
partial def iterate [Monad m] (f : m α) : MLList m α :=
  squash fun _ => return cons (← f) (iterate f)

/-- Repeatedly apply a function `f : α → m (α × List β)` to an initial `a : α`,
accumulating the elements of the resulting `List β` as a single monadic lazy list.

(This variant allows starting with a specified `List β` of elements, as well. )-/
partial def fixlWith [Monad m] {α β : Type u} (f : α → m (α × List β))
    (s : α) (l : List β) : MLList m β :=
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
def fixl [Monad m] {α β : Type u} (f : α → m (α × List β)) (s : α) : MLList m β :=
  fixlWith f s []

/-- Compute, inside the monad, whether a `MLList` is empty. -/
def isEmpty [Monad m] (xs : MLList m α) : m (ULift Bool) :=
  (ULift.up ∘ Option.isSome) <$> uncons xs

/-- Convert a `List` to a `MLList`. -/
def ofList : List α → MLList m α
  | [] => nil
  | h :: t => cons h (thunk fun _ => ofList t)

/-- Convert a `List` of values inside the monad into a `MLList`. -/
def ofListM [Monad m] : List (m α) → MLList m α
  | [] => nil
  | h :: t => squash fun _ => return cons (← h) (ofListM t)

/-- Extract a list inside the monad from a `MLList`. -/
partial def force [Monad m] (L : MLList m α) : m (List α) := do
  match ← L.uncons with
  | none => pure []
  | some (x, xs) => return x :: (← xs.force)

/-- Extract an array inside the monad from a `MLList`. -/
def asArray [Monad m] (L : MLList m α) : m (Array α) := do
  let mut r := #[]
  for a in L do
    r := r.push a
  return r

/-- Performs a monadic case distinction on a `MLList` when the motive is a `MLList` as well. -/
@[specialize]
def casesM [Monad m] (xs : MLList m α)
    (hnil : Unit → m (MLList m β)) (hcons : α → MLList m α → m (MLList m β)) : MLList m β :=
  squash fun _ => do
    match ← xs.uncons with
    | none => hnil ()
    | some (x, xs) => hcons x xs

/--
Performs a case distinction on a `MLList` when the motive is a `MLList` as well.
(We need to be in a monadic context to distinguish a nil from a cons.)
-/
@[specialize]
def cases [Monad m] (xs : MLList m α)
    (hnil : Unit → MLList m β) (hcons : α → MLList m α → MLList m β) : MLList m β :=
  match xs.uncons? with
  | none => xs.casesM (fun _ => return hnil ()) (fun x xs => return hcons x xs)
  | some none => thunk hnil
  | some (some (x, xs)) => thunk fun _ => hcons x xs

/-- Gives the monadic lazy list consisting all of folds of a function on a given initial element.
Thus `[a₀, a₁, ...].foldsM f b` will give `[b, ← f b a₀, ← f (← f b a₀) a₁, ...]`. -/
partial def foldsM [Monad m] (f : β → α → m β) (init : β) (L : MLList m α) : MLList m β :=
  cons init <| squash fun _ => do
    match ← L.uncons with
    | none => return nil
    | some (x, xs) => return foldsM f (← f init x) xs

/-- Gives the monadic lazy list consisting all of folds of a function on a given initial element.
Thus `[a₀, a₁, ...].foldsM f b` will give `[b, f b a₀, f (f b a₀) a₁, ...]`. -/
def folds [Monad m] (f : β → α → β) (init : β) (L : MLList m α) : MLList m β :=
  L.foldsM (fun b a => pure (f b a)) init

/-- Take the first `n` elements, as a list inside the monad. -/
partial def takeAsList [Monad m] (xs : MLList m α) (n : Nat) : m (List α) :=
  go n [] xs
where
  /-- Implementation of `MLList.takeAsList`. -/
  go (r : Nat) (acc : List α) (xs : MLList m α) : m (List α) :=
    match r with
    | 0 => pure acc.reverse
    | r+1 => do match ← xs.uncons with
      | none => pure acc.reverse
      | some (x, xs) => go r (x :: acc) xs

/-- Take the first `n` elements, as an array inside the monad. -/
partial def takeAsArray [Monad m] (xs : MLList m α) (n : Nat) : m (Array α) :=
  go n #[] xs
where
  /-- Implementation of `MLList.takeAsArray`. -/
  go (r : Nat) (acc : Array α) (xs : MLList m α) : m (Array α) :=
    match r with
    | 0 => pure acc
    | r+1 => do match ← xs.uncons with
      | none => pure acc
      | some (x, xs) => go r (acc.push x) xs

/-- Take the first `n` elements. -/
partial def take [Monad m] (xs : MLList m α) : Nat → MLList m α
  | 0 => nil
  | n+1 => xs.cases (fun _ => nil) fun h l => cons h (l.take n)

/-- Drop the first `n` elements. -/
def drop [Monad m] (xs : MLList m α) : Nat → MLList m α
  | 0 => xs
  | n+1 => xs.cases (fun _ => nil) fun _ l => l.drop n

/-- Apply a function which returns values in the monad to every element of a `MLList`. -/
partial def mapM [Monad m] (f : α → m β) (xs : MLList m α) : MLList m β :=
  xs.cases (fun _ => nil) fun x xs => squash fun _ => return cons (← f x) (xs.mapM f)

/-- Apply a function to every element of a `MLList`. -/
def map [Monad m] (f : α → β) (L : MLList m α) : MLList m β :=
  L.mapM fun a => pure (f a)

/-- Filter a `MLList` using a monadic function. -/
partial def filterM [Monad m] (p : α → m (ULift Bool)) (L : MLList m α) : MLList m α :=
  L.casesM (fun _ => pure nil) fun x xs =>
    return if (← p x).down then cons x (filterM p xs) else filterM p xs

/-- Filter a `MLList`. -/
def filter [Monad m] (p : α → Bool) (L : MLList m α) : MLList m α :=
  L.filterM fun a => pure <| .up (p a)

/-- Filter and transform a `MLList` using a function that returns values inside the monad. -/
-- Note that the type signature has changed since Lean 3, when we allowed `f` to fail.
-- Use `try?` from `Mathlib.Control.Basic` to lift a possibly failing function to `Option`.
partial def filterMapM [Monad m] (f : α → m (Option β)) (xs : MLList m α) : MLList m β :=
  xs.casesM (fun _ => pure nil) fun x xs => do
    match ← f x with
    | none => return xs.filterMapM f
    | some a => return cons a (xs.filterMapM f)

/-- Filter and transform a `MLList` using an `Option` valued function. -/
def filterMap [Monad m] (f : α → Option β) : MLList m α → MLList m β :=
  filterMapM fun a => do pure (f a)

/-- Take the initial segment of the lazy list, until the function `f` first returns `false`. -/
partial def takeWhileM [Monad m] (f : α → m (ULift Bool)) (L : MLList m α) : MLList m α :=
  L.casesM (fun _ => pure nil) fun x xs =>
    return if !(← f x).down then nil else cons x (xs.takeWhileM f)

/-- Take the initial segment of the lazy list, until the function `f` first returns `false`. -/
def takeWhile [Monad m] (f : α → Bool) : MLList m α → MLList m α :=
  takeWhileM fun a => pure (.up (f a))

/-- Concatenate two monadic lazy lists. -/
partial def append [Monad m] (xs : MLList m α) (ys : Unit → MLList m α) : MLList m α :=
  xs.cases ys fun x xs => cons x (append xs ys)

/-- Join a monadic lazy list of monadic lazy lists into a single monadic lazy list. -/
partial def join [Monad m] (xs : MLList m (MLList m α)) : MLList m α :=
  xs.cases (fun _ => nil) fun x xs => append x (fun _ => join xs)

/-- Enumerate the elements of a monadic lazy list, starting at a specified offset. -/
partial def enumFrom [Monad m] (n : Nat) (xs : MLList m α) : MLList m (Nat × α) :=
  xs.cases (fun _ => nil) fun x xs => cons (n, x) (xs.enumFrom (n+1))

/-- Enumerate the elements of a monadic lazy list. -/
def enum [Monad m] : MLList m α → MLList m (Nat × α) := enumFrom 0

/-- The infinite monadic lazy list of natural numbers.-/
def range [Monad m] : MLList m Nat := MLList.fix (fun n => pure (n + 1)) 0

/-- Iterate through the elements of `Fin n`. -/
partial def fin (n : Nat) : MLList m (Fin n) := go 0 where
  /-- Implementation of `MLList.fin`. -/
  go (i : Nat) : MLList m (Fin n) :=
    if h : i < n then cons ⟨i, h⟩ (thunk fun _ => go (i+1)) else nil

/-- Convert an array to a monadic lazy list. -/
partial def ofArray {α : Type} (L : Array α) : MLList m α := go 0 where
  /-- Implementation of `MLList.ofArray`. -/
  go (i : Nat) : MLList m α :=
    if h : i < L.size then cons (L.get ⟨i, h⟩) (thunk fun _ => go (i+1)) else nil

/-- Group the elements of a lazy list into chunks of a given size.
If the lazy list is finite, the last chunk may be smaller (possibly even length 0). -/
partial def chunk [Monad m] (L : MLList m α) (n : Nat) : MLList m (Array α) := go n #[] L where
  /-- Implementation of `MLList.chunk`. -/
  go (r : Nat) (acc : Array α) (M : MLList m α) : MLList m (Array α) :=
    match r with
    | 0 => cons acc (thunk fun _ => go n #[] M)
    | r+1 => squash fun _ => do
      match ← M.uncons with
      | none => return cons acc nil
      | some (a, M') => return go r (acc.push a) M'

/-- Add one element to the end of a monadic lazy list. -/
def concat [Monad m] (L : MLList m α) (a : α) : MLList m α := L.append (fun _ => cons a nil)

/-- Take the product of two monadic lazy lists. -/
partial def zip [Monad m] (L : MLList m α) (M : MLList m β) : MLList.{u} m (α × β) :=
  L.cases (fun _ => nil) fun a L =>
  M.cases (fun _ => nil) fun b M =>
  cons (a, b) (L.zip M)

/-- Apply a function returning a monadic lazy list to each element of a monadic lazy list,
joining the results. -/
partial def bind [Monad m] (xs : MLList m α) (f : α → MLList m β) : MLList m β :=
  xs.cases (fun _ => nil) fun x xs =>
    match xs.uncons? with
    | some none => f x
    | _ => append (f x) (fun _ => bind xs f)

/-- Convert any value in the monad to the singleton monadic lazy list. -/
def monadLift [Monad m] (x : m α) : MLList m α :=
  squash fun _ => return cons (← x) nil

/-- Lift the monad of a lazy list. -/
partial def liftM [Monad m] [Monad n] [MonadLiftT m n] (L : MLList m α) : MLList n α :=
  squash fun _ =>
    return match ← (uncons L : m _) with
    | none => nil
    | some (a, L') => cons a L'.liftM

/-- Given a lazy list in a state monad, run it on some initial state, recording the states. -/
partial def runState [Monad m] (L : MLList (StateT.{u} σ m) α) (s : σ) : MLList m (α × σ) :=
  squash fun _ =>
    return match ← (uncons L).run s with
    | (none, _) => nil
    | (some (a, L'), s') => cons (a, s') (L'.runState s')

/-- Given a lazy list in a state monad, run it on some initial state. -/
def runState' [Monad m] (L : MLList (StateT.{u} σ m) α) (s : σ) : MLList m α :=
  L.runState s |>.map (·.1)

/-- Run a lazy list in a `ReaderT` monad on some fixed state. -/
partial def runReader [Monad m] (L : MLList (ReaderT.{u, u} ρ m) α) (r : ρ) :
    MLList m α :=
  squash fun _ =>
    return match ← (uncons L).run r with
    | none => nil
    | some (a, L') => cons a (L'.runReader r)

/-- Run a lazy list in a `StateRefT'` monad on some initial state. -/
partial def runStateRef [Monad m] [MonadLiftT (ST ω) m] (L : MLList (StateRefT' ω σ m) α) (s : σ) :
    MLList m α :=
  squash fun _ =>
    return match ← (uncons L).run s with
    | (none, _) => nil
    | (some (a, L'), s') => cons a (L'.runStateRef s')

/-- Return the head of a monadic lazy list if it exists, as an `Option` in the monad. -/
def head? [Monad m] (L : MLList m α) : m (Option α) := return (← L.uncons).map (·.1)

/-- Take the initial segment of the lazy list,
up to and including the first place where `f` gives `true`. -/
partial def takeUpToFirstM [Monad m] (L : MLList m α) (f : α → m (ULift Bool)) : MLList m α :=
  L.casesM (fun _ => pure nil) fun x xs =>
    return cons x <| if (← (f x)).down then nil else xs.takeUpToFirstM f

/-- Take the initial segment of the lazy list,
up to and including the first place where `f` gives `true`. -/
def takeUpToFirst [Monad m] (L : MLList m α) (f : α → Bool) : MLList m α :=
  L.takeUpToFirstM fun a => pure (.up (f a))

/-- Gets the last element of a monadic lazy list, as an option in the monad.
This will run forever if the list is infinite. -/
partial def getLast? [Monad m] (L : MLList m α) : m (Option α) := do
  match ← uncons L with
  | none => return none
  | some (x, xs) => aux x xs
where
  /-- Implementation of `MLList.aux`. -/
  aux (x : α) (L : MLList m α) : m (Option α) := do
    match ← uncons L with
    | none => return some x
    | some (y, ys) => aux y ys

/-- Gets the last element of a monadic lazy list, or the default value if the list is empty.
This will run forever if the list is infinite. -/
partial def getLast! [Monad m] [Inhabited α] (L : MLList m α) : m α := Option.get! <$> L.getLast?

/-- Folds a binary function across a monadic lazy list, from an initial starting value.
This will run forever if the list is infinite. -/
partial def foldM [Monad m] (f : β → α → m β) (init : β) (L : MLList m α) : m β :=
  return (← L.foldsM f init |>.getLast?).getD init -- `foldsM` is always non-empty, anyway.

/-- Folds a binary function across a monadic lazy list, from an initial starting value.
This will run forever if the list is infinite. -/
partial def fold [Monad m] (f : β → α → β) (init : β) (L : MLList m α) : m β :=
  L.foldM (fun b a => pure (f b a)) init

/--
Return the head of a monadic lazy list, as a value in the monad.
Fails if the list is empty.
-/
def head [Monad m] [Alternative m] (L : MLList m α) : m α := do
  let some (r, _) ← L.uncons | failure
  return r

/--
Apply a function returning values inside the monad to a monadic lazy list,
returning only the first successful result.
-/
def firstM [Monad m] [Alternative m] (L : MLList m α) (f : α → m (Option β)) : m β :=
  (L.filterMapM f).head

/-- Return the first value on which a predicate returns true. -/
def first [Monad m] [Alternative m] (L : MLList m α) (p : α → Bool) : m α := (L.filter p).head

instance [Monad m] : Monad (MLList m) where
  pure a := cons a nil
  map := map
  bind := bind

instance [Monad m] : Alternative (MLList m) where
  failure := nil
  orElse := MLList.append

instance [Monad m] : MonadLift m (MLList m) where
  monadLift := monadLift
