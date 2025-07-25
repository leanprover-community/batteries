import Batteries.Tactic.Lint

set_option linter.missingDocs false

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

-- The following `dsimp`-lemma is (correctly) not flagged by the linter
@[defeq, simp]
theorem foo_eq_ite (n : Nat) : foo n = if n = n then n else 0 := by
  rfl

end Equiv

namespace List

private axiom test_sorry : ∀ {α}, α

@[simp]
theorem ofFn_getElem_eq_map {β : Type _} (l : List α) (f : α → β) :
    ofFn (fun i : Fin l.length => f <| l[(i : Nat)]) = l.map f := test_sorry

example {β : Type _} (l : List α) (f : α → β) :
    ofFn (fun i : Fin l.length => f <| l[(i : Nat)]) = l.map f := by simp only [ofFn_getElem_eq_map]

end List

/-! This tests that `simpNF` is not accidentally using `quasiPatternApprox := true`. -/

def eqToFun {X Y : Type} (p : X = Y) : X → Y := by rw [p]; exact id

@[simp]
theorem eqToFun_comp_eq_self {β} {X : Type} {f : β → Type}
    (z : ∀ b, X → f b) {j j' : β} (w : j = j') :
    eqToFun (by simp [w]) ∘ z j' = z j := by
  cases w; rfl

@[simp]
theorem eqToFun_comp_iso_hom_eq_self {β} {X : Type} {f : β → Type}
    (z : ∀ b, X ≃ f b) {j j' : β} (w : j = j') :
    eqToFun (by simp [w]) ∘ (z j').toFun = (z j).toFun := by
  cases w; rfl

#lint- only simpNF
