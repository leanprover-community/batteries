import Std.Data.BitVec.Lemmas
import Std.Data.Fin.Iterate
import Std.Data.Nat.Lemmas

namespace Std.BitVec

/--
`iunfoldr f a` returns
-/
def iunfoldr (f : Fin w -> α → α × Bool) (a:α) : α × BitVec w :=
  Fin.hIterate (fun i => α × BitVec i) (a, nil) fun i q =>
    (fun p => ⟨p.fst, cons p.snd q.snd⟩) (f i q.fst)

theorem iunfoldr.fst_eq
    {w:Nat}
    {f : Fin w → α → α × Bool}
    (state : Nat → α)
    (s : α)
    (init : s = state 0)
    (ind : ∀(i:Fin w), (f i (state i.val)).fst = state (i.val+1))
    : (iunfoldr f s).fst = state w := by
  unfold iunfoldr
  apply Fin.hIterate_elim (fun i (p : α × BitVec i) => p.fst = state i)
  case init =>
    exact init
  case step =>
    intro i ⟨s, v⟩ p
    simp at p
    simp [p, ind i]

private theorem iunfoldr.eq_test
    {w:Nat}
    {f : Fin w → α → α × Bool}
    (state : Nat → α)
    (value : BitVec w)
    (a : α)
    (init : state 0 = a)
    (step : ∀(i:Fin w), f i (state i.val) = (state (i.val+1), value.getLsb i.val))
    : iunfoldr f a = (state w, BitVec.truncate w value) := by
  apply Fin.hIterate_eq (fun i => ((state i, BitVec.truncate i value) : α × BitVec i))
  case init =>
    simp only [init, eq_nil]
  case step =>
    intro i
    simp
    apply And.intro
    case left =>
      simp [step]
    case right =>
      simp [step, cons_getLsb_truncate]

theorem iunfoldr_replace
    {w:Nat}
    {f : Fin w → α → α × Bool}
    (state : Nat → α)
    (value : BitVec w)
    (a : α)
    (init : state 0 = a)
    (step : ∀(i:Fin w), f i (state i.val) = (state (i.val+1), value.getLsb i.val))
    : iunfoldr f a = (state w, value) := by
  have h := iunfoldr.eq_test state value a init step
  simp [h]
