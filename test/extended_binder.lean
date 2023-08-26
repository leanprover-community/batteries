import Std.Classes.SetNotation
import Std.Tactic.GuardMsgs

namespace Test

/-- info: ∃ a, a ≤ 1 ∧ a < 2 : Prop -/
#guard_msgs in
#check ∃ a ≤ 1, a < 2

/-- info: ∃ a, a ≤ 1 ∧ a < 2 : Prop -/
#guard_msgs in
#check ∃ᵉ (a ≤ 1), a < 2

/-- info: ∃ a, a ≤ 1 ∧ ∃ b, b ≤ 2 ∧ a = b : Prop -/
#guard_msgs in
#check ∃ᵉ (a ≤ 1) (b ≤ 2), a = b

/-- info: ∀ (a : Nat), a ≤ 1 → ∀ (b : Nat), b ≤ 2 → a = b : Prop -/
#guard_msgs in
#check ∀ᵉ (a ≤ 1) (b ≤ 2), a = b

/-- info: ∃ x, x ≤ 2 ∧ True : Prop -/
#guard_msgs in
#check ∃ᵉ _ ≤ 2, True

/-- info: ∀ (x : Nat), x ≤ 2 → True : Prop -/
#guard_msgs in
#check ∀ᵉ _ ≤ 2, True

structure Foo where n : Nat
instance : LE Foo := ⟨fun a b => a.n ≤ b.n⟩

/--
info: fun n =>
  ∃ x,
    x ≤ n ∧
      match x with
      | { n := a } => a = 1 : Foo → Prop
-/
#guard_msgs in
#check fun (n : Foo) => ∃ ⟨a⟩ ≤ n, a = 1

/--
info: ∃ x,
  match x with
  | (a, b) => a = b : Prop
-/
#guard_msgs in
#check ∃ᵉ ⟨a, b⟩ : Nat × Nat, a = b

/--
info: ∃ x,
  match x with
  | (a, b) => a = b : Prop
-/
#guard_msgs in
#check ∃ᵉ (⟨a, b⟩ : Nat × Nat), a = b

/--
info: ∃ x,
  match x with
  | (a, b) =>
    ∃ x,
      match x with
      | (c, d) => a + d = b + c : Prop
-/
#guard_msgs in
#check ∃ᵉ (⟨a, b⟩ : Nat × Nat) (⟨c, d⟩ : Nat × Nat), a + d = b + c

/-- Sets -/
def Set (α : Type _) := α → Prop
instance : Membership α (Set α) := ⟨fun x s => s x⟩

/-- info: ∀ (s : Set Nat) (x : Nat), x ∈ s → x = 0 : Prop -/
#guard_msgs in
#check ∀ᵉ (s : Set Nat) (x ∈ s), x = 0

/--
info: ∀ (s : Set (Nat × Nat)) (x : Nat × Nat),
  x ∈ s →
    match x with
    | (a, b) => a ≤ b : Prop
-/
#guard_msgs in
#check ∀ᵉ (s : Set (Nat × Nat)) (⟨a, b⟩ ∈ s), a ≤ b
