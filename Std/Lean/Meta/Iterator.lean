import Lean.Meta.Basic

namespace Lean.Meta

/--
Provides an iterface for iterating over values that are defined in a particular
meta state.
-/
structure Iterator (α : Type) where
  /-- Function for getting next value and state pair. -/
  next : MetaM (Option (α × Meta.SavedState))

namespace Iterator

/--
Convert a list into an iterator with the current state.
-/
def ofList (l : List α) : MetaM (Iterator α) := do
  let s ← saveState
  let ref ← IO.mkRef l
  let next := do
    restoreState s
    match ← ref.get with
    | [] =>
      pure none
    | r :: l =>
      ref.set l
      pure <| some (r, ←saveState)
  pure { next }

/--
Map and filter results of iterator and returning only those values returned
by `f`.
-/
partial def filterMapM (f : α → MetaM (Option β)) (L : Iterator α) : Iterator β :=
    { next := _next }
  where _next := do
    match ← L.next with
    | none =>
      pure none
    | some (v, s) =>
      restoreState s
      let r ← f v
      match r with
      | none =>
        _next
      | some r =>
        pure <| some (r, ←saveState)

/--
Find the first alternative in a nondeterministic value, as a monadic value.
-/
def head (L : Iterator α) : MetaM α := do
  match ← L.next with
  | none =>
    failure
  | some (x, s) =>
    restoreState s
    pure x

/--
Return the first value returned by the iterator that `f` succeeds on.
-/
def firstM (L : Iterator α) (f : α → MetaM (Option β)) : MetaM β := L.filterMapM f |>.head

end Iterator

end Lean.Meta
