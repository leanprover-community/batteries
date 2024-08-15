import Batteries.Tactic.Congr

section congr

example (c : Prop → Prop → Prop → Prop) (x x' y z z' : Prop)
    (h₀ : x ↔ x') (h₁ : z ↔ z') : c x y z ↔ c x' y z' := by
  apply Iff.of_eq -- FIXME: not needed in lean 3
  congr
  · guard_target =ₐ x = x'
    apply_ext_theorem
    assumption
  · guard_target =ₐ z = z'
    ext
    assumption

example {α β γ δ} {F : ∀ {α β}, (α → β) → γ → δ} {f g : α → β} {s : γ}
    (h : ∀ x : α, f x = g x) : F f s = F g s := by
  congr with x
  -- apply_assumption -- FIXME
  apply h

example {α β : Type _} {f : _ → β} {x y : { x : { x : α // x = x } // x = x }}
    (h : x.1 = y.1) : f x = f y := by
  congr with : 1
  exact h

example {α β : Type _} {F : _ → β} {f g : { f : α → β // f = f }}
    (h : ∀ x : α, (f : α → β) x = (g : α → β) x) : F f = F g := by
  rcongr x
  revert x
  guard_target = type_of% h
  exact h

section

-- Adaptation note: the next two examples have always failed if `List.ext` was in scope,
-- but until nightly-2024-04-24 (when `List.ext` was upstreamed), it wasn't in scope.
-- In order to preserve the test behaviour we locally remove the `ext` attribute.
attribute [-ext] List.ext_getElem?

private opaque List.sum : List Nat → Nat

example {ls : List Nat} :
    (ls.map fun x => (ls.map fun y => 1 + y).sum + 1) =
    (ls.map fun x => (ls.map fun y => Nat.succ y).sum + 1) := by
  rcongr (_x y)
  guard_target =ₐ 1 + y = y.succ
  rw [Nat.add_comm]

example {ls : List Nat} {f g : Nat → Nat} {h : ∀ x, f x = g x} :
    (ls.map fun x => f x + 3) = ls.map fun x => g x + 3 := by
  rcongr x
  exact h x

end

-- succeed when either `ext` or `congr` can close the goal
example : () = () := by rcongr

example : 0 = 0 := by rcongr

example {α} (a : α) : a = a := by congr

example : { f : Nat → Nat // f = id } :=
  ⟨_, by
    congr (config := { closePre := false, closePost := false }) with x
    exact Nat.zero_add x⟩

-- FIXME(?): congr doesn't fail
-- example {α} (a b : α) (h : False) : a = b := by
--   fail_if_success congr
--   cases h

end congr
