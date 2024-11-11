import Batteries.Lean.SatisfiesM
import Batteries.Data.Array.Monadic
import Batteries.Data.List.Monadic

open Lean Meta Array Elab Term Tactic Command

-- For now these live in the test file, as it's not really clear we want people relying on them!
instance : LawfulMonad (EIO ε) := inferInstanceAs <| LawfulMonad (EStateM _ _)
instance : LawfulMonad BaseIO := inferInstanceAs <| LawfulMonad (EIO _)
instance : LawfulMonad IO := inferInstanceAs <| LawfulMonad (EIO _)
instance : LawfulMonad CoreM :=
  inferInstanceAs <| LawfulMonad (ReaderT _ <| StateRefT' _ _ (EIO Exception))
instance : LawfulMonad MetaM :=
  inferInstanceAs <| LawfulMonad (ReaderT _ <| StateRefT' _ _ CoreM)
instance : LawfulMonad TermElabM :=
  inferInstanceAs <| LawfulMonad (ReaderT _ <| StateRefT' _ _ MetaM)
instance : LawfulMonad TacticM :=
  inferInstanceAs <| LawfulMonad (ReaderT _ $ StateRefT' _ _ $ TermElabM)
instance : LawfulMonad CommandElabM :=
  inferInstanceAs <| LawfulMonad (ReaderT _ $ StateRefT' _ _ $ EIO _)

example (xs : Array Expr) : MetaM { ts : Array Expr // ts.size = xs.size } := do
  let r ← satisfying (xs.size_mapM inferType)
  return r

def addRandomEvens (n : Nat) (k : Nat) : IO Nat := do
  let mut r := k
  for _ in List.range n do
    r := r + 2 * (← IO.rand 0 37)
  pure r

theorem addRandomEvens_spec (n k) : SatisfiesM (fun r => r % 2 = k % 2) (addRandomEvens n k) := by
  rw [addRandomEvens]
  simp [List.forIn_yield_eq_foldlM]
  apply List.SatisfiesM_foldlM
  · rfl
  · intros b w a m
    apply SatisfiesM.bind_pre
    simp_all [SatisfiesM_EStateM_eq, EStateM.run]

def addRandomEvens' (n : Nat) (k : Nat) : IO { r : Nat // r % 2 = k % 2 } := do
  satisfying (addRandomEvens_spec n k)
