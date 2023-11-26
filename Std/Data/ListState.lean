/-
Copyright (c) 2023 J. W. Gerbscheid. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: J. W. Gerbscheid

The combined list and state monad transformer.
`ListStateT σ α` is equivalent to `StateT σ (ListT α)` but more efficient.
-/

/-- List-like type to avoid extra level of indirection -/
inductive StateList (σ α : Type u) where
  | nil : StateList σ α
  | cons : α → σ → StateList σ α → StateList σ α

namespace StateList

variable {α σ : Type u}

def toList : StateList σ α → List (α × σ)
  | .cons a s l => (a, s) :: l.toList
  | .nil => []

def toList' : StateList σ α → List α
  | .cons a _ l => a :: l.toList'
  | .nil => []

def map (f : α → β) : StateList σ α → StateList σ β
  | .cons a s l   => .cons (f a) s (l.map f)
  | .nil => .nil

def reverseAux : StateList σ α → StateList σ α → StateList σ α
  | .nil,   r => r
  | .cons a s l, r => reverseAux l (.cons a s r)

def reverse (l : StateList σ α) : StateList σ α :=
  reverseAux l .nil

def append : (xs ys : StateList σ α) → StateList σ α
  | .nil,         bs => bs
  | .cons a s l, bs => .cons a s (l.append bs)

instance : Append (StateList σ α) := ⟨StateList.append⟩

@[specialize]
def foldlM {m : Type u → Type v} [Monad m] {β : Type u} {α σ : Type w} : (f : β → α → σ → m β) → (init : β) → StateList σ α → m β
  | _, b, .nil     => pure b
  | f, b, .cons a s l => do
    let s' ← f b a s
    StateList.foldlM f s' l

@[inline]
def foldrM {m : Type u → Type v} [Monad m] {b : Type u} {α σ : Type w} (f : α → σ → b → m b) (init : b) (l : StateList σ α) : m b :=
  l.reverse.foldlM (fun b a s => f a s b) init

end StateList

def ListStateT (σ : Type u) (m : Type u → Type v) (α : Type u) : Type (max u v) :=
  σ → m (StateList σ α)

@[always_inline, inline]
def ListStateT.run {σ : Type u} {m : Type u → Type v} [Functor m] {α : Type u} (x : ListStateT σ m α) (s : σ) : m (List (α × σ)) :=
  StateList.toList <$> x s

@[always_inline, inline]
def ListStateT.run' {σ : Type u} {m : Type u → Type v} [Functor m] {α : Type u} (x : ListStateT σ m α) (s : σ) : m (List α) :=
  StateList.toList' <$> x s

@[reducible]
def ListStateM (σ α : Type u) : Type u := ListStateT σ Id α

namespace ListStateT
section
variable {σ : Type u} {m : Type u → Type v}
variable [Monad m] {α β : Type u}

@[always_inline, inline]
protected def pure (a : α) : ListStateT σ m α :=
  fun s => return StateList.nil.cons a s

@[always_inline, inline]
protected def bind (x : ListStateT σ m α) (f : α → ListStateT σ m β) : ListStateT σ m β :=
  fun s => do
    (← x s).foldrM (fun a s bs => return (← f a s) ++ bs) .nil

@[always_inline, inline]
protected def map (f : α → β) (x : ListStateT σ m α) : ListStateT σ m β :=
  fun s => StateList.map f <$> x s

@[always_inline]
instance : Monad (ListStateT σ m) where
  pure := ListStateT.pure
  bind := ListStateT.bind
  map  := ListStateT.map

@[always_inline, inline]
protected def orElse {α : Type u} (x : ListStateT σ m α) (y : Unit → ListStateT σ m α) : ListStateT σ m α :=
  fun s => (· ++ ·) <$> x s <*> y () s

@[always_inline, inline]
protected def failure {α : Type u} : ListStateT σ m α :=
  fun _ => pure .nil

instance [Alternative m] : Alternative (ListStateT σ m) where
  failure := ListStateT.failure
  orElse  := ListStateT.orElse

@[always_inline, inline]
protected def get : ListStateT σ m σ :=
  fun s => return StateList.nil.cons s s

@[always_inline, inline]
protected def set : σ → ListStateT σ m PUnit :=
  fun s' _ => return StateList.nil.cons ⟨⟩ s'

@[always_inline, inline]
protected def modifyGet (f : σ → α × σ) : ListStateT σ m α :=
  fun s => let (a, s) := f s; return StateList.nil.cons a s

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
