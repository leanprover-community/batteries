/-
Copyright (c) 2023 J. W. Gerbscheid. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: J. W. Gerbscheid

The list monad transformer
-/

def ListT (m : Type u → Type v) (α : Type u) : Type v :=
  m (List α)

@[always_inline, inline]
def ListT.run {m : Type u → Type v} {α : Type u} (x : ListT m α) : m (List α) :=
  x

namespace ListT
variable {m : Type u → Type v} [Monad m] {α β : Type u}

protected def mk (x : m (List α)) : ListT m α :=
  x

@[always_inline, inline]
protected def pure (a : α) : ListT m α := ListT.mk do
  pure [a]

@[always_inline, inline]
protected def bind (x : ListT m α) (f : α → ListT m β) : ListT m β := ListT.mk do
  (← x).foldrM (fun a bs => (· ++ bs) <$> f a) []

@[always_inline, inline]
protected def map (f : α → β) (x : ListT m α) : ListT m β := ListT.mk do
  List.map f <$> x

@[always_inline]
instance : Monad (ListT m) where
  pure := ListT.pure
  bind := ListT.bind
  map  := ListT.map

@[always_inline, inline]
protected def orElse {α : Type u} (x : ListT m α) (y : Unit → ListT m α) : ListT m α := ListT.mk do
  (· ++ ·) <$> x <*> y ()

@[always_inline, inline]
protected def failure {α : Type u} : ListT m α := ListT.mk do
  pure []

instance [Alternative m] : Alternative (ListT m) where
  failure := ListT.failure
  orElse  := ListT.orElse

@[always_inline, inline]
protected def lift {α : Type u} (t : m α) : ListT m α := ListT.mk do
  let a ← t; return [a]

instance : MonadLift m (ListT m) := ⟨ListT.lift⟩

@[always_inline]
instance (m) [Monad m] : MonadFunctor m (ListT m) := ⟨fun f x => f x⟩

@[always_inline]
instance (ε) [MonadExceptOf ε m] : MonadExceptOf ε (ListT m) := {
  throw    := fun x => ListT.lift do throwThe ε x
  tryCatch := fun x c => ListT.mk do tryCatchThe ε x c
}

@[always_inline]
instance ListT.monadControl (m : Type u → Type v) [Monad m] : MonadControl m (ListT m) where
  stM        := List
  liftWith f := liftM <| f fun x => x.run
  restoreM x := x

end ListT
