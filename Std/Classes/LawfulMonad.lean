/-
Copyright (c) 2022 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Std.Logic

/--
An alternative constructor for `LawfulMonad` which has more
defaultable fields in the common case.
-/
theorem LawfulMonad.mk' (m : Type u → Type v) [Monad m]
    (id_map : ∀ {α} (x : m α), id <$> x = x)
    (pure_bind : ∀ {α β} (x : α) (f : α → m β), pure x >>= f = f x)
    (bind_assoc : ∀ {α β γ} (x : m α) (f : α → m β) (g : β → m γ),
      x >>= f >>= g = x >>= fun x => f x >>= g)
    (map_const : ∀ {α β} (x : α) (y : m β),
      Functor.mapConst x y = Function.const β x <$> y := by intros; rfl)
    (seqLeft_eq : ∀ {α β} (x : m α) (y : m β),
      x <* y = (x >>= fun a => y >>= fun _ => pure a) := by intros; rfl)
    (seqRight_eq : ∀ {α β} (x : m α) (y : m β), x *> y = (x >>= fun _ => y) := by intros; rfl)
    (bind_pure_comp : ∀ {α β} (f : α → β) (x : m α),
      x >>= (fun y => pure (f y)) = f <$> x := by intros; rfl)
    (bind_map : ∀ {α β} (f : m (α → β)) (x : m α), f >>= (. <$> x) = f <*> x := by intros; rfl)
    : LawfulMonad m :=
  have map_pure {α β} (g : α → β) (x : α) : g <$> (pure x : m α) = pure (g x) := by
    rw [← bind_pure_comp]; simp [pure_bind]
  { id_map, bind_pure_comp, bind_map, pure_bind, bind_assoc, map_pure,
    comp_map := by simp [← bind_pure_comp, bind_assoc, pure_bind]
    pure_seq := by intros; rw [← bind_map]; simp [pure_bind]
    seq_pure := by intros; rw [← bind_map]; simp [map_pure, bind_pure_comp]
    seq_assoc := by simp [← bind_pure_comp, ← bind_map, bind_assoc, pure_bind]
    map_const := funext fun x => funext (map_const x)
    seqLeft_eq := by simp [seqLeft_eq, ← bind_map, ← bind_pure_comp, pure_bind, bind_assoc]
    seqRight_eq := fun x y => by
      rw [seqRight_eq, ← bind_map, ← bind_pure_comp, bind_assoc]; simp [pure_bind, id_map] }

instance : LawfulMonad (Except ε) := LawfulMonad.mk'
  (id_map := fun x => by cases x <;> rfl)
  (pure_bind := fun a f => rfl)
  (bind_assoc := fun a f g => by cases a <;> rfl)

instance : LawfulApplicative (Except ε) := inferInstance
instance : LawfulFunctor (Except ε) := inferInstance

instance : LawfulMonad Option := LawfulMonad.mk'
  (id_map := fun x => by cases x <;> rfl)
  (pure_bind := fun x f => rfl)
  (bind_assoc := fun x f g => by cases x <;> rfl)
  (bind_pure_comp := fun f x => by cases x <;> rfl)

instance : LawfulApplicative Option := inferInstance
instance : LawfulFunctor Option := inferInstance


instance : LawfulMonad (EStateM ε σ) := .mk'
  (id_map := fun x => funext <| fun s => by
    dsimp only [EStateM.instMonadEStateM, EStateM.map]
    match x s with
    | .ok _ _ => rfl
    | .error _ _ => rfl)
  (pure_bind := fun _ _ => rfl)
  (bind_assoc := fun x _ _ => funext <| fun s => by
    dsimp only [EStateM.instMonadEStateM, EStateM.bind]
    match x s with
    | .ok _ _ => rfl
    | .error _ _ => rfl)
  (map_const := fun _ _ => rfl)

instance : LawfulMonad (EIO ε) := inferInstanceAs <| LawfulMonad (EStateM _ _)
instance : LawfulMonad BaseIO := inferInstanceAs <| LawfulMonad (EIO _)
instance : LawfulMonad IO := inferInstance

instance : LawfulMonad (EST ε σ) := inferInstanceAs <| LawfulMonad (EStateM _ _)
instance : LawfulMonad (ST ε) := inferInstance

/-!
## SatisfiesM

The `SatisfiesM` predicate works over an arbitrary (lawful) monad / applicative / functor,
and enables Hoare-like reasoning over monadic expressions. For example, given a monadic
function `f : α → m β`, to say that the return value of `f` satisfies `Q` whenever
the input satisfies `P`, we write `∀ a, P a → SatisfiesM Q (f a)`.
-/

/--
`SatisfiesM p (x : m α)` lifts propositions over a monad. It asserts that `x` may as well
have the type `x : m {a // p a}`, because there exists some `m {a // p a}` whose image is `x`.
So `p` is the postcondition of the monadic value.
-/
def SatisfiesM {m : Type u → Type v} [Functor m] (p : α → Prop) (x : m α) : Prop :=
  ∃ x' : m {a // p a}, Subtype.val <$> x' = x

namespace SatisfiesM

/-- If `p` is always true, then every `x` satisfies it. -/
theorem of_true [Applicative m] [LawfulApplicative m] {x : m α}
    (h : ∀ a, p a) : SatisfiesM p x :=
  ⟨(fun a => ⟨a, h a⟩) <$> x, by simp [← comp_map, Function.comp_def]⟩

/--
If `p` is always true, then every `x` satisfies it.
(This is the strongest postcondition version of `of_true`.)
-/
protected theorem trivial [Applicative m] [LawfulApplicative m] {x : m α} :
  SatisfiesM (fun _ => True) x := of_true fun _ => trivial

/-- The `SatisfiesM p x` predicate is monotonic in `p`. -/
theorem imp [Functor m] [LawfulFunctor m] {x : m α}
    (h : SatisfiesM p x) (H : ∀ {a}, p a → q a) : SatisfiesM q x :=
  let ⟨x, h⟩ := h; ⟨(fun ⟨a, h⟩ => ⟨_, H h⟩) <$> x, by rw [← h, ← comp_map]; rfl⟩

/-- `SatisfiesM` distributes over `<$>`, general version. -/
protected theorem map [Functor m] [LawfulFunctor m] {x : m α}
    (hx : SatisfiesM p x) (hf : ∀ {a}, p a → q (f a)) : SatisfiesM q (f <$> x) := by
  let ⟨x', hx⟩ := hx
  refine ⟨(fun ⟨a, h⟩ => ⟨f a, hf h⟩) <$> x', ?_⟩
  rw [← hx]; simp [← comp_map, Function.comp_def]

/--
`SatisfiesM` distributes over `<$>`, strongest postcondition version.
(Use this for reasoning forward from assumptions.)
-/
theorem map_post [Functor m] [LawfulFunctor m] {x : m α}
    (hx : SatisfiesM p x) : SatisfiesM (fun b => ∃ a, p a ∧ b = f a) (f <$> x) :=
  hx.map fun h => ⟨_, h, rfl⟩

/--
`SatisfiesM` distributes over `<$>`, weakest precondition version.
(Use this for reasoning backward from the goal.)
-/
theorem map_pre [Functor m] [LawfulFunctor m] {x : m α}
    (hx : SatisfiesM (fun a => p (f a)) x) : SatisfiesM p (f <$> x) :=
  hx.map fun h => h

/-- `SatisfiesM` distributes over `mapConst`, general version. -/
protected theorem mapConst [Functor m] [LawfulFunctor m] {x : m α}
    (hx : SatisfiesM q x) (ha : ∀ {b}, q b → p a) : SatisfiesM p (Functor.mapConst a x) :=
  map_const (f := m) ▸ hx.map ha

/-- `SatisfiesM` distributes over `pure`, general version / weakest precondition version. -/
protected theorem pure [Applicative m] [LawfulApplicative m]
    (h : p a) : SatisfiesM (m := m) p (pure a) := ⟨pure ⟨_, h⟩, by simp⟩

/-- `SatisfiesM` distributes over `<*>`, general version. -/
protected theorem seq [Applicative m] [LawfulApplicative m] {x : m α}
    (hf : SatisfiesM p₁ f) (hx : SatisfiesM p₂ x)
    (H : ∀ {f a}, p₁ f → p₂ a → q (f a)) : SatisfiesM q (f <*> x) := by
  match f, x, hf, hx with | _, _, ⟨f, rfl⟩, ⟨x, rfl⟩ => ?_
  refine ⟨(fun ⟨a, h₁⟩ ⟨b, h₂⟩ => ⟨a b, H h₁ h₂⟩) <$> f <*> x, ?_⟩
  simp only [← pure_seq]; simp [SatisfiesM, seq_assoc]
  simp only [← pure_seq]; simp [seq_assoc, Function.comp_def]

/-- `SatisfiesM` distributes over `<*>`, strongest postcondition version. -/
protected theorem seq_post [Applicative m] [LawfulApplicative m] {x : m α}
    (hf : SatisfiesM p₁ f) (hx : SatisfiesM p₂ x) :
    SatisfiesM (fun c => ∃ f a, p₁ f ∧ p₂ a ∧ c = f a) (f <*> x) :=
  hf.seq hx fun  hf ha => ⟨_, _, hf, ha, rfl⟩

/--
`SatisfiesM` distributes over `<*>`, weakest precondition version 1.
(Use this when `x` and the goal are known and `f` is a subgoal.)
-/
protected theorem seq_pre [Applicative m] [LawfulApplicative m] {x : m α}
    (hf : SatisfiesM (fun f => ∀ {a}, p₂ a → q (f a)) f) (hx : SatisfiesM p₂ x) :
    SatisfiesM q (f <*> x) :=
  hf.seq hx fun hf ha => hf ha

/--
`SatisfiesM` distributes over `<*>`, weakest precondition version 2.
(Use this when `f` and the goal are known and `x` is a subgoal.)
-/
protected theorem seq_pre' [Applicative m] [LawfulApplicative m] {x : m α}
    (hf : SatisfiesM p₁ f) (hx : SatisfiesM (fun a => ∀ {f}, p₁ f → q (f a)) x) :
    SatisfiesM q (f <*> x) :=
  hf.seq hx fun hf ha => ha hf

/-- `SatisfiesM` distributes over `<*`, general version. -/
protected theorem seqLeft [Applicative m] [LawfulApplicative m] {x : m α}
    (hx : SatisfiesM p₁ x) (hy : SatisfiesM p₂ y)
    (H : ∀ {a b}, p₁ a → p₂ b → q a) : SatisfiesM q (x <* y) :=
  seqLeft_eq x y ▸ (hx.map fun h _ => H h).seq_pre hy

/-- `SatisfiesM` distributes over `*>`, general version. -/
protected theorem seqRight [Applicative m] [LawfulApplicative m] {x : m α}
    (hx : SatisfiesM p₁ x) (hy : SatisfiesM p₂ y)
    (H : ∀ {a b}, p₁ a → p₂ b → q b) : SatisfiesM q (x *> y) :=
  seqRight_eq x y ▸ (hx.map fun h _ => H h).seq_pre hy

/-- `SatisfiesM` distributes over `>>=`, general version. -/
protected theorem bind [Monad m] [LawfulMonad m] {f : α → m β}
    (hx : SatisfiesM p x) (hf : ∀ a, p a → SatisfiesM q (f a)) :
    SatisfiesM q (x >>= f) := by
  match x, hx with | _, ⟨x, rfl⟩ => ?_
  have g a ha := Classical.indefiniteDescription _ (hf a ha)
  refine ⟨x >>= fun ⟨a, h⟩ => g a h, ?_⟩
  simp [← bind_pure_comp]; congr; funext ⟨a, h⟩; simp [← (g a h).2, ← bind_pure_comp]

/-- `SatisfiesM` distributes over `>>=`, weakest precondition version. -/
protected theorem bind_pre [Monad m] [LawfulMonad m] {f : α → m β}
    (hx : SatisfiesM (fun a => SatisfiesM q (f a)) x) :
    SatisfiesM q (x >>= f) := hx.bind fun _ h => h

end SatisfiesM

@[simp] theorem SatisfiesM_Id_eq : SatisfiesM (m := Id) p x ↔ p x :=
  ⟨fun ⟨y, eq⟩ => eq ▸ y.2, fun h => ⟨⟨_, h⟩, rfl⟩⟩

@[simp] theorem SatisfiesM_Option_eq : SatisfiesM (m := Option) p x ↔ ∀ a, x = some a → p a :=
  ⟨by revert x; intro | some _, ⟨some ⟨_, h⟩, rfl⟩, _, rfl => exact h,
   fun h => match x with | some a => ⟨some ⟨a, h _ rfl⟩, rfl⟩ | none => ⟨none, rfl⟩⟩

@[simp] theorem SatisfiesM_Except_eq : SatisfiesM (m := Except ε) p x ↔ ∀ a, x = .ok a → p a :=
  ⟨by revert x; intro | .ok _, ⟨.ok ⟨_, h⟩, rfl⟩, _, rfl => exact h,
   fun h => match x with | .ok a => ⟨.ok ⟨a, h _ rfl⟩, rfl⟩ | .error e => ⟨.error e, rfl⟩⟩

@[simp] theorem SatisfiesM_ReaderT_eq [Monad m] :
    SatisfiesM (m := ReaderT ρ m) p x ↔ ∀ s, SatisfiesM p (x s) :=
  (exists_congr fun a => by exact ⟨fun eq _ => eq ▸ rfl, funext⟩).trans Classical.skolem.symm

theorem SatisfiesM_StateRefT_eq [Monad m] :
    SatisfiesM (m := StateRefT' ω σ m) p x ↔ ∀ s, SatisfiesM p (x s) := by simp

@[simp] theorem SatisfiesM_StateT_eq [Monad m] [LawfulMonad m] :
    SatisfiesM (m := StateT ρ m) (α := α) p x ↔ ∀ s, SatisfiesM (m := m) (p ·.1) (x s) := by
  refine .trans ⟨fun ⟨f, eq⟩ => eq ▸ ?_, fun ⟨f, h⟩ => ?_⟩ Classical.skolem.symm
  · refine ⟨fun s => (fun ⟨⟨a, h⟩, s'⟩ => ⟨⟨a, s'⟩, h⟩) <$> f s, fun s => ?_⟩
    rw [← comp_map, map_eq_pure_bind]; rfl
  · refine ⟨fun s => (fun ⟨⟨a, s'⟩, h⟩ => ⟨⟨a, h⟩, s'⟩) <$> f s, funext fun s => ?_⟩
    show _ >>= _ = _; simp [map_eq_pure_bind, ← h]

@[simp] theorem SatisfiesM_ExceptT_eq [Monad m] [LawfulMonad m] :
    SatisfiesM (m := ExceptT ρ m) (α := α) p x ↔ SatisfiesM (m := m) (∀ a, · = .ok a → p a) x := by
  refine ⟨fun ⟨f, eq⟩ => eq ▸ ?_, fun ⟨f, eq⟩ => eq ▸ ?_⟩
  · exists (fun | .ok ⟨a, h⟩ => ⟨.ok a, fun | _, rfl => h⟩ | .error e => ⟨.error e, fun.⟩) <$> f
    show _ = _ >>= _; rw [← comp_map, map_eq_pure_bind]; congr; funext a; cases a <;> rfl
  · exists ((fun | ⟨.ok a, h⟩ => .ok ⟨a, h _ rfl⟩ | ⟨.error e, _⟩ => .error e) <$> f : m _)
    show _ >>= _ = _; simp [← comp_map, map_eq_pure_bind]; congr; funext ⟨a, h⟩; cases a <;> rfl
