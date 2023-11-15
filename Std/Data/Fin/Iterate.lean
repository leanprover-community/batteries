/-
Copyright (c) 2023 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joe Hendrix
-/
import Std.Logic

namespace Fin

/--
`hIterate` is a heterogenous iterative operation that applies a
index-dependent function `f` to a value `init : P start` a total of
`stop - start` times to produce a value of type `P stop`.

Concretely, `hIterate start stop f init` is equal to
```lean
  init |> f start _ |> f (start+1) _ ... |> f (end-1) _
```

Because it is heterogenous and must return a value of type `P stop`,
`hIterate` requires proof that `start ≤ stop`.

One can prove properties of `hIterate` using the general theorem
`hIterate_elim` or other more specialzied theorems.
 -/
def hIterate (P : Nat → Sort _)
             {n : Nat}
             (init : P 0)
             (f : ∀(i:Fin n), P i.val → P (i.val+1))
             : P n :=
    let rec loop (i : Nat) (ubnd : i ≤ n) (a : P i) : P n :=
            if g : i < n then
              loop (i+1) g (f ⟨i, g⟩ a)
            else
              have p : i = n := (or_iff_left g).mp (Nat.eq_or_lt_of_le ubnd)
              cast (congrArg P p) a
    loop 0 (Nat.zero_le n) init
  termination_by loop i _ _ => n - i

private theorem hIterate_loop_elim
    {P : Nat → Sort _}
    (Q : ∀(i:Nat), P i → Prop)
    {n  : Nat}
    (f : ∀(i:Fin n), P i.val → P (i.val+1))
    {i : Nat}
    (ubnd : i ≤ n)
    (s : P i)
    (init : Q i s)
    (step : ∀(k:Fin n) (s:P k.val), Q k.val s → Q (k.val+1) (f k s))
    : Q n (hIterate.loop P f i ubnd s) := by
  let ⟨j, p⟩ := Nat.le.dest ubnd
  induction j generalizing i ubnd init with
  | zero =>
    unfold hIterate.loop
    have g : ¬ (i < n) := by simp at p; simp [p]
    simp [g]
    have r : Q n (cast (congrArg P p) s) :=
      @Eq.rec Nat i (fun k eq => Q k (cast (congrArg P eq) s)) init n p
    exact r
  | succ j inv =>
    unfold hIterate.loop
    have d : Nat.succ i + j = n := by simp [Nat.succ_add]; exact p
    have g : i < n := Nat.le.intro d
    simp [g]
    exact inv _ _ (step ⟨i,g⟩ s init) d

/-
`hIterate_elim` provides a mechanism for showing that the result of
`hIterate` satisifies a property `Q stop` by showing that the states
at the intermediate indices `i : start ≤ i < stop` satisfy `Q i`.
-/
theorem hIterate_elim
    {P : Nat → Sort _}
    (Q : ∀(i:Nat), P i → Prop)
    {n : Nat}
    (f : ∀(i:Fin n), P i.val → P (i.val+1))
    (s : P 0)
    (init : Q 0 s)
    (step : ∀(k:Fin n) (s:P k.val), Q k.val s → Q (k.val+1) (f k s))
    : Q n (hIterate P s f) := by
  exact hIterate_loop_elim _ _ _ _ init step

/-
`hIterate_eq`provides a mechanism for replacing hIterate with another
function overshowing that the result of
`hIterate` satisifies a property `Q stop` by showing that the states
at the intermediate indices `i : start ≤ i < stop` satisfy `Q i`.
-/
theorem hIterate_eq
    {P : Nat → Sort _}
    (state : ∀(i:Nat), P i)
    {n : Nat}
    (f : ∀(i:Fin n), P i.val → P (i.val+1))
    (s : P 0)
    (init : s = state 0)
    (step : ∀(i:Fin n), f i (state i) = state (i+1))
    : hIterate P s f = state n := by
  apply hIterate_elim (fun i s => s = state i) f s init
  intro i s s_eq
  simp only [s_eq, step]
