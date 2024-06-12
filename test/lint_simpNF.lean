import Batteries.Tactic.Lint

set_option linter.missingDocs false

protected def Sum.elim {α β γ : Sort _} (f : α → γ) (g : β → γ) : Sum α β → γ :=
  fun x => Sum.casesOn x f g

structure Equiv (α : Sort _) (β : Sort _) where
  toFun : α → β
  invFun : β → α

infixl:25 " ≃ " => Equiv

namespace Equiv

instance : CoeFun (α ≃ β) fun _ => α → β := ⟨toFun⟩

protected def symm (e : α ≃ β) : β ≃ α := ⟨e.invFun, e.toFun⟩

def sumCompl {α : Type _} (p : α → Prop) [DecidablePred p] :
    Sum { a // p a } { a // ¬p a } ≃ α where
  toFun := Sum.elim Subtype.val Subtype.val
  invFun a := if h : p a then Sum.inl ⟨a, h⟩ else Sum.inr ⟨a, h⟩

@[simp]
theorem sumCompl_apply_symm_of_pos (p : α → Prop) [DecidablePred p] (a : α) (h : p a) :
    (sumCompl p).symm a = Sum.inl ⟨a, h⟩ :=
  dif_pos h

def foo (n : Nat) : Nat := if n = n then n else 0

@[simp]
theorem foo_eq_id : foo = id := by
  funext n
  simp [foo]

-- The following `dsimp`-lemma is flagged by the linter
@[simp]
theorem foo_eq_ite (n : Nat) : foo n = if n = n then n else 0 := by
  rfl

end Equiv

/--
error: /- The `simpNF` linter reports:
SOME SIMP LEMMAS ARE NOT IN SIMP-NORMAL FORM.
see note [simp-normal form] for tips how to debug this.
https://leanprover-community.github.io/mathlib_docs/notes.html#simp-normal%20form -/
#check Equiv.foo_eq_ite /- simp can prove this:
  by simp only [Equiv.foo_eq_id, @id_eq, @ite_true]
One of the lemmas above could be a duplicate.
If that's not the case try reordering lemmas or adding @[priority].
 -/
-/
#guard_msgs in
#lint- only simpNF
