import Std.Tactic.AC

/-- Test for [lean4#1202](https://github.com/leanprover/lean4/issues/1202) -/

opaque f : Bool → Bool → Bool
axiom f_comm (a b : Bool) : f a b = f b a
axiom f_assoc (a b c : Bool) : f (f a b) c = f a (f b c)
instance : Std.Commutative f := ⟨f_comm⟩
instance : Std.Associative f := ⟨f_assoc⟩

example (a b c : Bool) : f (f a b) c = f (f a c) b :=
  by ac_rfl -- good

example (a b c : Bool) : (f (f a b) c = f (f a c) b) ∧ true :=
  And.intro (by ac_rfl) rfl -- good

example (a b c : Bool) : (f (f a b) c = f (f a c) b) ∧ true := by
  apply And.intro
  . ac_rfl
    /-
    tactic 'refl' failed, refl failed
    case left
    a b c : Bool
    ⊢ f (f a b) c = f (f a c) b
    -/
  . rfl
