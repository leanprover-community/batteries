/-
Copyright (c) 2022 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Batteries.Data.RBMap.WF

/-!
# Path operations; `modify` and `alter`

This develops the necessary theorems to construct the `modify` and `alter` functions on `RBSet`
using path operations for in-place modification of an `RBTree`.
-/

namespace Batteries

namespace RBNode
open RBColor

attribute [simp] Path.fill

/-! ## path balance -/

/-- Asserts that property `p` holds on the root of the tree, if any. -/
def OnRoot (p : α → Prop) : RBNode α → Prop
  | nil => True
  | node _ _ x _ => p x

namespace Path

/-- Same as `fill` but taking its arguments in a pair for easier composition with `zoom`. -/
@[inline] def fill' : RBNode α × Path α → RBNode α := fun (t, path) => path.fill t

theorem zoom_fill' (cut : α → Ordering) (t : RBNode α) (path : Path α) :
    fill' (zoom cut t path) = path.fill t := by
  induction t generalizing path with
  | nil => rfl
  | node _ _ _ _ iha ihb => unfold zoom; split <;> [apply iha; apply ihb; rfl]

theorem zoom_fill (H : zoom cut t path = (t', path')) : path.fill t = path'.fill t' :=
  (H ▸ zoom_fill' cut t path).symm

variable (c₀ : RBColor) (n₀ : Nat) in
/--
The balance invariant for a path. `path.Balanced c₀ n₀ c n` means that `path` is a red-black tree
with balance invariant `c₀, n₀`, but it has a "hole" where a tree with balance invariant `c, n`
has been removed. The defining property is `Balanced.fill`: if `path.Balanced c₀ n₀ c n` and you
fill the hole with a tree satisfying `t.Balanced c n`, then `(path.fill t).Balanced c₀ n₀` .
-/
protected inductive Balanced : Path α → RBColor → Nat → Prop where
  /-- The root of the tree is `c₀, n₀`-balanced by assumption. -/
  | protected root : Path.root.Balanced c₀ n₀
  /-- Descend into the left subtree of a red node. -/
  | redL : Balanced y black n → parent.Balanced red n →
    (Path.left red parent v y).Balanced black n
  /-- Descend into the right subtree of a red node. -/
  | redR : Balanced x black n → parent.Balanced red n →
    (Path.right red x v parent).Balanced black n
  /-- Descend into the left subtree of a black node. -/
  | blackL : Balanced y c₂ n → parent.Balanced black (n + 1) →
    (Path.left black parent v y).Balanced c₁ n
  /-- Descend into the right subtree of a black node. -/
  | blackR : Balanced x c₁ n → parent.Balanced black (n + 1) →
    (Path.right black x v parent).Balanced c₂ n

/--
The defining property of a balanced path: If `path` is a `c₀,n₀` tree with a `c,n` hole,
then filling the hole with a `c,n` tree yields a `c₀,n₀` tree.
-/
protected theorem Balanced.fill {path : Path α} {t} :
    path.Balanced c₀ n₀ c n → t.Balanced c n → (path.fill t).Balanced c₀ n₀
  | .root, h => h
  | .redL hb H, ha | .redR ha H, hb => H.fill (.red ha hb)
  | .blackL hb H, ha | .blackR ha H, hb => H.fill (.black ha hb)

protected theorem _root_.Batteries.RBNode.Balanced.zoom : t.Balanced c n → path.Balanced c₀ n₀ c n →
    zoom cut t path = (t', path') → ∃ c n, t'.Balanced c n ∧ path'.Balanced c₀ n₀ c n
  | .nil, hp => fun e => by cases e; exact ⟨_, _, .nil, hp⟩
  | .red ha hb, hp => by
    unfold zoom; split
    · exact ha.zoom (.redL hb hp)
    · exact hb.zoom (.redR ha hp)
    · intro e; cases e; exact ⟨_, _, .red ha hb, hp⟩
  | .black ha hb, hp => by
    unfold zoom; split
    · exact ha.zoom (.blackL hb hp)
    · exact hb.zoom (.blackR ha hp)
    · intro e; cases e; exact ⟨_, _, .black ha hb, hp⟩

protected theorem Balanced.ins {path : Path α}
    (hp : path.Balanced c₀ n₀ c n) (ht : t.RedRed (c = red) n) :
    ∃ n, (path.ins t).Balanced black n := by
  induction hp generalizing t with
  | root => exact ht.setBlack
  | redL hr hp ih => match ht with
    | .balanced .nil => exact ih (.balanced (.red .nil hr))
    | .balanced (.red ha hb) => exact ih (.redred rfl (.red ha hb) hr)
    | .balanced (.black ha hb) => exact ih (.balanced (.red (.black ha hb) hr))
  | redR hl hp ih => match ht with
    | .balanced .nil => exact ih (.balanced (.red hl .nil))
    | .balanced (.red ha hb) => exact ih (.redred rfl hl (.red ha hb))
    | .balanced (.black ha hb) => exact ih (.balanced (.red hl (.black ha hb)))
  | blackL hr _hp ih => exact have ⟨c, h⟩ := ht.balance1 hr; ih (.balanced h)
  | blackR hl _hp ih => exact have ⟨c, h⟩ := ht.balance2 hl; ih (.balanced h)

protected theorem Balanced.insertNew {path : Path α} (H : path.Balanced c n black 0) :
    ∃ n, (path.insertNew v).Balanced black n := H.ins (.balanced (.red .nil .nil))

protected theorem Balanced.del {path : Path α}
    (hp : path.Balanced c₀ n₀ c n) (ht : t.DelProp c' n) (hc : c = black → c' ≠ red) :
    ∃ n, (path.del t c').Balanced black n := by
  induction hp generalizing t c' with
  | root => match c', ht with
    | red, ⟨_, h⟩ | black, ⟨_, _, h⟩ => exact h.setBlack
  | @redL _ n _ _ hb hp ih => match c', n, ht with
    | red, _, _ => cases hc rfl rfl
    | black, _, ⟨_, rfl, ha⟩ => exact ih ((hb.balLeft ha).of_false nofun) nofun
  | @redR _ n _ _ ha hp ih => match c', n, ht with
    | red, _, _ => cases hc rfl rfl
    | black, _, ⟨_, rfl, hb⟩ => exact ih ((ha.balRight hb).of_false nofun) nofun
  | @blackL _ _ n _ _ _ hb hp ih => match c', n, ht with
    | red, _, ⟨_, ha⟩ => exact ih ⟨_, rfl, .redred ⟨⟩ ha hb⟩ nofun
    | black, _, ⟨_, rfl, ha⟩ => exact ih ⟨_, rfl, (hb.balLeft ha).imp fun _ => ⟨⟩⟩ nofun
  | @blackR _ _ n _ _ _ ha hp ih =>  match c', n, ht with
    | red, _, ⟨_, hb⟩ => exact ih ⟨_, rfl, .redred ⟨⟩ ha hb⟩ nofun
    | black, _, ⟨_, rfl, hb⟩ => exact ih ⟨_, rfl, (ha.balRight hb).imp fun _ => ⟨⟩⟩ nofun

/--
The property of a path returned by `t.zoom cut`. Each of the parents visited along the path have
the appropriate ordering relation to the cut.
-/
def Zoomed (cut : α → Ordering) : Path α → Prop
  | .root => True
  | .left _ parent x _ => cut x = .lt ∧ parent.Zoomed cut
  | .right _ _ x parent => cut x = .gt ∧ parent.Zoomed cut

theorem zoom_zoomed₂ (e : zoom cut t path = (t', path'))
    (hp : path.Zoomed cut) : path'.Zoomed cut :=
  match t, e with
  | nil, rfl => hp
  | node .., e => by
    revert e; unfold zoom; split
    · next h => exact fun e => zoom_zoomed₂ e ⟨h, hp⟩
    · next h => exact fun e => zoom_zoomed₂ e ⟨h, hp⟩
    · intro e; cases e; exact hp

/--
`path.RootOrdered cmp v` is true if `v` would be able to fit into the hole
without violating the ordering invariant.
-/
def RootOrdered (cmp : α → α → Ordering) : Path α → α → Prop
  | .root, _ => True
  | .left _ parent x _, v => cmpLT cmp v x ∧ parent.RootOrdered cmp v
  | .right _ _ x parent, v => cmpLT cmp x v ∧ parent.RootOrdered cmp v

theorem _root_.Batteries.RBNode.cmpEq.RootOrdered_congr
    {cmp : α → α → Ordering} (h : cmpEq cmp a b) :
    ∀ {t : Path α}, t.RootOrdered cmp a ↔ t.RootOrdered cmp b
  | .root => .rfl
  | .left .. => and_congr h.lt_congr_left h.RootOrdered_congr
  | .right .. => and_congr h.lt_congr_right h.RootOrdered_congr

theorem Zoomed.toRootOrdered {cmp} :
    ∀ {path : Path α}, path.Zoomed (cmp v) → path.RootOrdered cmp v
  | .root, h => h
  | .left .., ⟨h, hp⟩ => ⟨⟨h⟩, hp.toRootOrdered⟩
  | .right .., ⟨h, hp⟩ => ⟨⟨OrientedCmp.cmp_eq_gt.1 h⟩, hp.toRootOrdered⟩

/-- The ordering invariant for a `Path`. -/
def Ordered (cmp : α → α → Ordering) : Path α → Prop
  | .root => True
  | .left _ parent x b => parent.Ordered cmp ∧
    b.All (cmpLT cmp x ·) ∧ parent.RootOrdered cmp x ∧
    b.All (parent.RootOrdered cmp) ∧ b.Ordered cmp
  | .right _ a x parent => parent.Ordered cmp ∧
    a.All (cmpLT cmp · x) ∧ parent.RootOrdered cmp x ∧
    a.All (parent.RootOrdered cmp) ∧ a.Ordered cmp

protected theorem Ordered.fill : ∀ {path : Path α} {t},
    (path.fill t).Ordered cmp ↔ path.Ordered cmp ∧ t.Ordered cmp ∧ t.All (path.RootOrdered cmp)
  | .root, _ => ⟨fun H => ⟨⟨⟩, H, .trivial ⟨⟩⟩, (·.2.1)⟩
  | .left .., _ => by
    simp [Ordered.fill, RBNode.Ordered, Ordered, RootOrdered, All_and]
    exact ⟨
      fun ⟨hp, ⟨ax, xb, ha, hb⟩, ⟨xp, ap, bp⟩⟩ => ⟨⟨hp, xb, xp, bp, hb⟩, ha, ⟨ax, ap⟩⟩,
      fun ⟨⟨hp, xb, xp, bp, hb⟩, ha, ⟨ax, ap⟩⟩ => ⟨hp, ⟨ax, xb, ha, hb⟩, ⟨xp, ap, bp⟩⟩⟩
  | .right .., _ => by
    simp [Ordered.fill, RBNode.Ordered, Ordered, RootOrdered, All_and]
    exact ⟨
      fun ⟨hp, ⟨ax, xb, ha, hb⟩, ⟨xp, ap, bp⟩⟩ => ⟨⟨hp, ax, xp, ap, ha⟩, hb, ⟨xb, bp⟩⟩,
      fun ⟨⟨hp, ax, xp, ap, ha⟩, hb, ⟨xb, bp⟩⟩ => ⟨hp, ⟨ax, xb, ha, hb⟩, ⟨xp, ap, bp⟩⟩⟩

theorem _root_.Batteries.RBNode.Ordered.zoom' {t : RBNode α} {path : Path α}
    (ht : t.Ordered cmp) (hp : path.Ordered cmp) (tp : t.All (path.RootOrdered cmp))
    (pz : path.Zoomed cut) (eq : t.zoom cut path = (t', path')) :
    t'.Ordered cmp ∧ path'.Ordered cmp ∧ t'.All (path'.RootOrdered cmp) ∧ path'.Zoomed cut :=
  have ⟨hp', ht', tp'⟩ := Ordered.fill.1 <| zoom_fill eq ▸ Ordered.fill.2 ⟨hp, ht, tp⟩
  ⟨ht', hp', tp', zoom_zoomed₂ eq pz⟩

theorem _root_.Batteries.RBNode.Ordered.zoom {t : RBNode α}
    (ht : t.Ordered cmp) (eq : t.zoom cut = (t', path')) :
    t'.Ordered cmp ∧ path'.Ordered cmp ∧ t'.All (path'.RootOrdered cmp) ∧ path'.Zoomed cut :=
  ht.zoom' (path := .root) ⟨⟩ (.trivial ⟨⟩) ⟨⟩ eq

theorem Ordered.ins : ∀ {path : Path α} {t : RBNode α},
    t.Ordered cmp → path.Ordered cmp → t.All (path.RootOrdered cmp) → (path.ins t).Ordered cmp
  | .root, t, ht, _, _ => Ordered.setBlack.2 ht
  | .left red parent x b, a, ha, ⟨hp, xb, xp, bp, hb⟩, H => by
    unfold ins; have ⟨ax, ap⟩ := All_and.1 H; exact hp.ins ⟨ax, xb, ha, hb⟩ ⟨xp, ap, bp⟩
  | .right red a x parent, b, hb, ⟨hp, ax, xp, ap, ha⟩, H => by
    unfold ins; have ⟨xb, bp⟩ := All_and.1 H; exact hp.ins ⟨ax, xb, ha, hb⟩ ⟨xp, ap, bp⟩
  | .left black parent x b, a, ha, ⟨hp, xb, xp, bp, hb⟩, H => by
    unfold ins; have ⟨ax, ap⟩ := All_and.1 H
    exact hp.ins (ha.balance1 ax xb hb) (balance1_All.2 ⟨xp, ap, bp⟩)
  | .right black a x parent, b, hb, ⟨hp, ax, xp, ap, ha⟩, H => by
    unfold ins; have ⟨xb, bp⟩ := All_and.1 H
    exact hp.ins (ha.balance2 ax xb hb) (balance2_All.2 ⟨xp, ap, bp⟩)

theorem Ordered.insertNew {path : Path α} (hp : path.Ordered cmp) (vp : path.RootOrdered cmp v) :
    (path.insertNew v).Ordered cmp :=
  hp.ins ⟨⟨⟩, ⟨⟩, ⟨⟩, ⟨⟩⟩ ⟨vp, ⟨⟩, ⟨⟩⟩

theorem Ordered.del : ∀ {path : Path α} {t : RBNode α} {c},
    t.Ordered cmp → path.Ordered cmp → t.All (path.RootOrdered cmp) → (path.del t c).Ordered cmp
  | .root, t, _, ht, _, _ => Ordered.setBlack.2 ht
  | .left _ parent x b, a, red, ha, ⟨hp, xb, xp, bp, hb⟩, H => by
    unfold del; have ⟨ax, ap⟩ := All_and.1 H; exact hp.del ⟨ax, xb, ha, hb⟩ ⟨xp, ap, bp⟩
  | .right _ a x parent, b, red, hb, ⟨hp, ax, xp, ap, ha⟩, H => by
    unfold del; have ⟨xb, bp⟩ := All_and.1 H; exact hp.del ⟨ax, xb, ha, hb⟩ ⟨xp, ap, bp⟩
  | .left _ parent x b, a, black, ha, ⟨hp, xb, xp, bp, hb⟩, H => by
    unfold del; have ⟨ax, ap⟩ := All_and.1 H
    exact hp.del (ha.balLeft ax xb hb) (ap.balLeft xp bp)
  | .right _ a x parent, b, black, hb, ⟨hp, ax, xp, ap, ha⟩, H => by
    unfold del; have ⟨xb, bp⟩ := All_and.1 H
    exact hp.del (ha.balRight ax xb hb) (ap.balRight xp bp)

end Path

/-! ## alter -/

/-- The `alter` function preserves the ordering invariants. -/
protected theorem Ordered.alter {t : RBNode α}
    (H : ∀ {x t' p}, t.zoom cut = (t', p) → f t'.root? = some x →
      p.RootOrdered cmp x ∧ t'.OnRoot (cmpEq cmp x))
    (h : t.Ordered cmp) : (alter cut f t).Ordered cmp := by
  simp [alter]; split
  · next path eq =>
    have ⟨_, hp, _, _⟩ := h.zoom eq; split
    · exact h
    · next hf => exact hp.insertNew (H eq hf).1
  · next path eq =>
    have ⟨⟨ax, xb, ha, hb⟩, hp, ⟨_, ap, bp⟩, _⟩ := h.zoom eq; split
    · exact hp.del (ha.append ax xb hb) (ap.append bp)
    · next hf =>
      have ⟨yp, xy⟩ := H eq hf
      apply Path.Ordered.fill.2
      exact ⟨hp, ⟨ax.imp xy.lt_congr_right.2, xb.imp xy.lt_congr_left.2, ha, hb⟩, yp, ap, bp⟩

/-- The `alter` function preserves the balance invariants. -/
protected theorem Balanced.alter {t : RBNode α}
    (h : t.Balanced c n) : ∃ c n, (t.alter cut f).Balanced c n := by
  simp [alter]; split
  · next path eq =>
    split
    · exact ⟨_, _, h⟩
    · have ⟨_, _, .nil, h⟩ := h.zoom .root eq
      exact ⟨_, h.insertNew⟩
  · next path eq =>
    have ⟨_, _, h, hp⟩ := h.zoom .root eq
    split
    · match h with
      | .red ha hb => exact ⟨_, hp.del ((ha.append hb).of_false (· rfl rfl)) nofun⟩
      | .black ha hb => exact ⟨_, hp.del ⟨_, rfl, (ha.append hb).imp fun _ => ⟨⟩⟩ nofun⟩
    · match h with
      | .red ha hb => exact ⟨_, _, hp.fill (.red ha hb)⟩
      | .black ha hb => exact ⟨_, _, hp.fill (.black ha hb)⟩

theorem modify_eq_alter (t : RBNode α) : t.modify cut f = t.alter cut (.map f) := by
  simp [modify, alter]

/-- The `modify` function preserves the ordering invariants. -/
protected theorem Ordered.modify {t : RBNode α}
    (H : (t.zoom cut).1.OnRoot fun x => cmpEq cmp (f x) x)
    (h : t.Ordered cmp) : (modify cut f t).Ordered cmp :=
  modify_eq_alter _ ▸ h.alter @fun
    | _, .node .., _, eq, rfl => by
      rw [eq] at H; exact ⟨H.RootOrdered_congr.2 (h.zoom eq).2.2.1.1, H⟩

/-- The `modify` function preserves the balance invariants. -/
protected theorem Balanced.modify {t : RBNode α}
    (h : t.Balanced c n) : ∃ c n, (t.modify cut f).Balanced c n := modify_eq_alter _ ▸ h.alter

theorem WF.alter {t : RBNode α}
    (H : ∀ {x t' p}, t.zoom cut = (t', p) → f t'.root? = some x →
      p.RootOrdered cmp x ∧ t'.OnRoot (cmpEq cmp x))
    (h : WF cmp t) : WF cmp (alter cut f t) :=
  let ⟨h₁, _, _, h₂⟩ := h.out; WF_iff.2 ⟨h₁.alter H, h₂.alter⟩

theorem WF.modify {t : RBNode α}
    (H : (t.zoom cut).1.OnRoot fun x => cmpEq cmp (f x) x)
    (h : WF cmp t) : WF cmp (t.modify cut f) :=
  let ⟨h₁, _, _, h₂⟩ := h.out; WF_iff.2 ⟨h₁.modify H, h₂.modify⟩

theorem find?_eq_zoom : ∀ {t : RBNode α} (p := .root), t.find? cut = (t.zoom cut p).1.root?
  | .nil, _ => rfl
  | .node .., _ => by unfold find? zoom; split <;> [apply find?_eq_zoom; apply find?_eq_zoom; rfl]

end RBNode

namespace RBSet
open RBNode

/--
A sufficient condition for `ModifyWF` is that the new element compares equal to the original.
-/
theorem ModifyWF.of_eq {t : RBSet α cmp}
    (H : ∀ {x}, RBNode.find? cut t.val = some x → cmpEq cmp (f x) x) : ModifyWF t cut f := by
  refine ⟨.modify ?_ t.2⟩
  revert H; rw [find?_eq_zoom]
  cases (t.1.zoom cut).1 <;> intro H <;> [trivial; exact H rfl]

end RBSet

namespace RBMap

/--
`O(log n)`. In-place replace the corresponding to key `k`.
This takes the element out of the tree while `f` runs,
so it uses the element linearly if `t` is unshared.
-/
def modify (t : RBMap α β cmp) (k : α) (f : β → β) : RBMap α β cmp :=
  @RBSet.modifyP _ _ t (cmp k ·.1) (fun (a, b) => (a, f b))
    (.of_eq fun _ => ⟨OrientedCmp.cmp_refl (cmp := Ordering.byKey Prod.fst cmp)⟩)

/-- Auxiliary definition for `alter`. -/
def alter.adapt (k : α) (f : Option β → Option β) : Option (α × β) → Option (α × β)
  | none =>
    match f none with
    | none => none
    | some v => some (k, v)
  | some (k', v') =>
    match f (some v') with
    | none => none
    | some v => some (k', v)

/--
`O(log n)`. `alterP cut f t` simultaneously handles inserting, erasing and replacing an element
using a function `f : Option α → Option α`. It is passed the result of `t.findP? cut`
and can either return `none` to remove the element or `some a` to replace/insert
the element with `a` (which must have the same ordering properties as the original element).

The element is used linearly if `t` is unshared.

The `AlterWF` assumption is required because `f` may change
the ordering properties of the element, which would break the invariants.
-/
@[specialize] def alter
    (t : RBMap α β cmp) (k : α) (f : Option β → Option β) : RBMap α β cmp := by
  refine @RBSet.alterP _ _ t (cmp k ·.1) (alter.adapt k f) ⟨.alter (@fun _ t' p eq => ?_) t.2⟩
  cases t' <;> simp [alter.adapt, RBNode.root?] <;> split <;> intro h <;> cases h
  · exact ⟨(t.2.out.1.zoom eq).2.2.2.toRootOrdered, ⟨⟩⟩
  · refine ⟨(?a).RootOrdered_congr.2 (t.2.out.1.zoom eq).2.2.1.1, ?a⟩
    exact ⟨OrientedCmp.cmp_refl (cmp := Ordering.byKey Prod.fst cmp)⟩

end RBMap
