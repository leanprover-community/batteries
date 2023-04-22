/-
Copyright (c) 2023 Miyahara Kō. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miyahara Kō
-/
import Std.Tactic.Lint.Misc

/-- `Accs r` is consisted of all accessible elements by `r`. -/
structure Accs.{u} {α : Sort u} (r : α → α → Prop) where
  /-- The accessible value. -/
  val : α
  /-- All elements in `Accs r` are accessible. -/
  acc : Acc r val

namespace Accs

universe u
variable {α : Sort u} {r : α → α → Prop}

/-- The subrelation of `r` on this type is well-founded. -/
@[nolint defLemma]
def wf : WellFounded (InvImage r (val : Accs r → α)) := ⟨fun ac => InvImage.accessible _ ac.acc⟩

instance wfRel : WellFoundedRelation (Accs r) where
  rel := InvImage r (val : Accs r → α)
  wf  := Accs.wf

end Accs

namespace Acc

universe v u
variable {α : Sort u} {r : α → α → Prop}

/-- A computable version of `Acc.rec`. Workaround until Lean has native support for this. -/
@[elab_as_elim]
def recC {motive : (a : α) → Acc r a → Sort v}
    (intro : (x : α) → (h : ∀ (y : α), r y x → Acc r y) →
     ((y : α) → (hr : r y x) → motive y (h y hr)) → motive x (intro x h))
    {a : α} (t : Acc r a) : motive a t :=
  intro a (fun x h => t.inv h) (fun y hr => recC intro (t.inv hr))
  termination_by recC a h => Accs.mk a h

theorem recC_intro {motive : (a : α) → Acc r a → Sort v}
    (intro : (x : α) → (h : ∀ (y : α), r y x → Acc r y) →
     ((y : α) → (hr : r y x) → motive y (h y hr)) → motive x (intro x h))
    {a : α} (h : ∀ (y : α), r y a → Acc r y) :
    recC intro (Acc.intro _ h) = intro a h (fun y hr => recC intro (h y hr)) :=
  rfl

@[csimp]
theorem rec_eq_recC : @Acc.rec = @Acc.recC := by
  funext α r motive intro a t
  induction t with
  | intro x h ih =>
    dsimp only [recC_intro intro h]
    congr
    funext y hr
    exact ih _ hr

/-- A computable version of `Acc.ndrec`. Workaround until Lean has native support for this. -/
abbrev ndrecC {C : α → Sort v}
    (m : (x : α) → ((y : α) → r y x → Acc r y) → ((y : α) → (a : r y x) → C y) → C x)
    {a : α} (n : Acc r a) : C a :=
  n.recC m

@[csimp]
theorem ndrec_eq_ndrecC : @Acc.ndrec = @Acc.ndrecC := by
  funext α r motive intro a t
  rw [Acc.ndrec, rec_eq_recC, Acc.ndrecC]

/-- A computable version of `Acc.ndrecOn`. Workaround until Lean has native support for this. -/
abbrev ndrecOnC {C : α → Sort v}
    {a : α} (n : Acc r a)
    (m : (x : α) → ((y : α) → r y x → Acc r y) → ((y : α) → (a : r y x) → C y) → C x) : C a :=
  n.recC m

@[csimp]
theorem ndrecOn_eq_ndrecOnC : @Acc.ndrecOn = @Acc.ndrecOnC := by
  funext α r motive intro a t
  rw [Acc.ndrecOn, rec_eq_recC, Acc.ndrecOnC]

end Acc

namespace WellFounded

universe u v
variable {α : Sort u}

/-- A computable version of `WellFounded.fixF`.
Workaround until Lean has native support for this. -/
def fixFC {r : α → α → Prop}
    {C : α → Sort v} (F : ∀ x, (∀ y, r y x → C y) → C x) (x : α) (a : Acc r x) : C x := by
  induction a using Acc.recC with
  | intro x₁ _ ih => exact F x₁ ih

@[csimp]
theorem fixF_eq_fixFC : @WellFounded.fixF = @WellFounded.fixFC := by
  funext α r C F x a
  rw [WellFounded.fixF, Acc.rec_eq_recC, WellFounded.fixFC]

/-- A computable version of `WellFounded.fix`.
Workaround until Lean has native support for this. -/
def fixC {C : α → Sort v} {r : α → α → Prop} (hwf : WellFounded r)
    (F : ∀ x, (∀ y, r y x → C y) → C x) (x : α) : C x :=
  fixFC F x (apply hwf x)

@[csimp]
theorem fix_eq_fixC : @WellFounded.fix = @WellFounded.fixC := by
  funext α C r hwf F x
  rw [WellFounded.fix, fixF_eq_fixFC, WellFounded.fixC]

end WellFounded
