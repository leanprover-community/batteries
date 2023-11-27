/-
Copyright (c) 2023 J. W. Gerbscheid. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: J. W. Gerbscheid

-/

/-- `StateList` is a List with a state associated to each element.
This is used instead of `List (α × σ)` as it is more efficient. -/
inductive StateList (σ α : Type u) where
  /-- .nil is the empty list. -/
  | nil : StateList σ α
  /-- If `a : α`, `s : σ` and `l : List α`, then `.cons a s l`, is the
  list with first element `a` with state `s` and `l` as the rest of the list. -/
  | cons : α → σ → StateList σ α → StateList σ α

namespace StateList

variable {α σ : Type u}

private def toList : StateList σ α → List (α × σ)
  | .cons a s l => (a, s) :: l.toList
  | .nil => []

private def toList' : StateList σ α → List α
  | .cons a _ l => a :: l.toList'
  | .nil => []

private def map (f : α → β) : StateList σ α → StateList σ β
  | .cons a s l   => .cons (f a) s (l.map f)
  | .nil => .nil

private def append : (xs ys : StateList σ α) → StateList σ α
  | .nil,         bs => bs
  | .cons a s l, bs => .cons a s (l.append bs)

instance : Append (StateList σ α) := ⟨StateList.append⟩

@[specialize]
private def foldrM {m : Type u → Type v} [Monad m] {β : Type u} {α σ : Type w} : (f : α → σ → β → m β) → (init : β) → StateList σ α → m β
  | _, b, .nil     => pure b
  | f, b, .cons a s l => do
    f a s (← l.foldrM f b)

end StateList

/-- The combined list and state monad transformer.
`ListStateT σ α` is equivalent to `StateT σ (ListT α)` but more efficient.

WARNING: `ListStateT σ α m` is only a monad if `m` is a commutative monad.
For example,
```
def problem : ListStateT Unit (StateM (Array Nat)) Unit := do
  Alternative.orElse (pure ()) (fun _ => pure ())
  ListStateT.lift $ modify (·.push 0)
  ListStateT.lift $ modify (·.push 1)

#eval ((problem.run' ()).run #[]).2
```
will yield either `#[0,1,0,1]`, or `#[0,0,1,1]`, depending on the order in which the actions
in the do block are combined.
-/
def ListStateT (σ : Type u) (m : Type u → Type v) (α : Type u) : Type (max u v) :=
  σ → m (StateList σ α)

/-- Run `x` on a given state `s`, returning the list of values with corresponding states. -/
@[always_inline, inline]
def ListStateT.run {σ : Type u} {m : Type u → Type v} [Functor m] {α : Type u} (x : ListStateT σ m α) (s : σ) : m (List (α × σ)) :=
  StateList.toList <$> x s

/-- Run `x` on a given state `s`, returning the list of values. -/
@[always_inline, inline]
def ListStateT.run' {σ : Type u} {m : Type u → Type v} [Functor m] {α : Type u} (x : ListStateT σ m α) (s : σ) : m (List α) :=
  StateList.toList' <$> x s

/-- The combined list and state monad. -/
@[reducible]
def ListStateM (σ α : Type u) : Type u := ListStateT σ Id α

namespace ListStateT
section
variable {σ : Type u} {m : Type u → Type v}
variable [Monad m] {α β : Type u}

@[always_inline, inline]
private def pure (a : α) : ListStateT σ m α :=
  fun s => return StateList.nil.cons a s

@[always_inline, inline]
private def bind (x : ListStateT σ m α) (f : α → ListStateT σ m β) : ListStateT σ m β :=
  fun s => do
    (← x s).foldrM (fun a s bs => return (← f a s) ++ bs) .nil

@[always_inline, inline]
private def map (f : α → β) (x : ListStateT σ m α) : ListStateT σ m β :=
  fun s => StateList.map f <$> x s

@[always_inline]
instance : Monad (ListStateT σ m) where
  pure := ListStateT.pure
  bind := ListStateT.bind
  map  := ListStateT.map

@[always_inline, inline]
private def orElse {α : Type u} (x : ListStateT σ m α) (y : Unit → ListStateT σ m α) : ListStateT σ m α :=
  fun s => (· ++ ·) <$> x s <*> y () s

@[always_inline, inline]
private def failure {α : Type u} : ListStateT σ m α :=
  fun _ => return .nil

instance : Alternative (ListStateT σ m) where
  failure := ListStateT.failure
  orElse  := ListStateT.orElse

/-- Return the state from `ListStateT σ m`. -/
@[always_inline, inline]
protected def get : ListStateT σ m σ :=
  fun s => return StateList.nil.cons s s

/-- Set the state in `ListStateT σ m`. -/
@[always_inline, inline]
protected def set : σ → ListStateT σ m PUnit :=
  fun s' _ => return StateList.nil.cons ⟨⟩ s'

/-- Modify and get the state in `ListStateT σ m`. -/
@[always_inline, inline]
protected def modifyGet (f : σ → α × σ) : ListStateT σ m α :=
  fun s => let a := f s; return StateList.nil.cons a.1 a.2

/-- Lift an action from `m α` to `ListStateT σ m α`. -/
@[always_inline, inline]
protected def lift {α : Type u} (t : m α) : ListStateT σ m α :=
  fun s => do let a ← t; return StateList.nil.cons a s

instance : MonadLift m (ListStateT σ m) := ⟨ListStateT.lift⟩

@[always_inline]
instance (σ m) [Monad m] : MonadFunctor m (ListStateT σ m) := ⟨fun f x s => f (x s)⟩

@[always_inline]
instance (ε) [MonadExceptOf ε m] : MonadExceptOf ε (ListStateT σ m) := {
  throw    := ListStateT.lift ∘ throwThe ε
  tryCatch := fun x c s => tryCatchThe ε (x s) (fun e => c e s)
}

end
end ListStateT

section
variable {σ : Type u} {m : Type u → Type v}

instance [Monad m] : MonadStateOf σ (ListStateT σ m) where
  get       := ListStateT.get
  set       := ListStateT.set
  modifyGet := ListStateT.modifyGet

end

@[always_inline]
instance ListStateT.monadControl (σ : Type u) (m : Type u → Type v) [Monad m] : MonadControl m (ListStateT σ m) where
  stM      := StateList σ
  liftWith := fun f => do let s ← get; liftM (f (fun x => x s))
  restoreM := fun x _ => x
