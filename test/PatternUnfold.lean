import Std.Tactic.PatternTactics.Unfold

@[irreducible] def f (n : Nat) : Nat := n + 1
-- unfold irreducible definitions
example (n : Nat) : f n = n + 1 := by
  unfold' f _
  rfl

-- occurrence indexing starts at 1
example (n : Nat) : f n = n + 1 := by
  unfold' (occs := 1) f _
  rfl

/-- error: occs indices should be positive integers -/
#guard_msgs in
example (n : Nat) : f n = n + 1 := by
  unfold' (occs := 0) f _
  rfl

example (n m : Nat) : f n + f m = f n + (m+1) := by
  unfold' (occs := 2) f _
  rfl

example (n m : Nat) : f n + f m = f n + (m+1) := by
  unfold' f m
  rfl

example (n m : Nat) : f n + f m = f n + f m := by
  unfold' (occs := 2 3) f _
  rfl

example (n m : Nat) : f n + f m = f n + f m := by
  unfold' (occs := 1 2) f _
  rfl

/--
error: unsolved goals
n m : Nat
⊢ Add.add n m = Add.add n m
-/
#guard_msgs in
example (n m : Nat) : n + m = Add.add n m := by
  unfold' n+m

/--
error: unsolved goals
n : Nat
f : Nat → Nat := fun x => x + 1
⊢ n + 1 = n + 1
-/
#guard_msgs in
example (n : Nat) : True := by
  let f : Nat → Nat := (· + 1)
  have : f n = n + 1 := by
    unfold' f _
  trivial

/--
error: unsolved goals
⊢ Nat.add = Nat.add
-/
#guard_msgs in
example : Nat.add = (fun a b => Nat.add a b) := by
  unfold' (occs := 1) fun _ => _

/--
error: tactic 'unfold'' failed, did not find instance of the pattern in the target expression{indendExpr p}
⊢ (fun x => x) = fun x => id x
-/
#guard_msgs in
example : (fun x : Nat => x) = fun x : Nat => id x := by
  unfold' id _

/--
error: unsolved goals
⊢ 1 + 1 = 1 + 1
-/
#guard_msgs in
example : 1+1 = let n := 1; n + n := by
  unfold' (occs := 2) let n := 1; n + n

/--
error: unsolved goals
a b : Nat
⊢ a = a
-/
#guard_msgs in
example (a b : Nat) : (a,b).1 = a := by
  unfold' (_,_).1

/--
error: unsolved goals
a b : Nat
⊢ a = a
-/
#guard_msgs in
example (a b : Nat) : (a,b).fst = a := by
  unfold' (_,_).fst
