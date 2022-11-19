/-
Copyright (c) 2022 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Std.Logic
import Std.Data.RBMap.Basic

/-!
# Lemmas for Red-black trees

The main theorem in this file is `WF_def`, which shows that the `RBNode.WF.mk` constructor
subsumes the others, by showing that `insert` and `erase` satisfy the red-black invariants.
-/

namespace Std

namespace RBNode
open RBColor

theorem cmpLt.trans (h₁ : cmpLt cmp x y) (h₂ : cmpLt cmp y z) : cmpLt cmp x z :=
  ⟨TransCmp.lt_trans h₁.1 h₂.1⟩

theorem cmpLt.trans_l {cmp x y} (H : cmpLt cmp x y) {t : RBNode α}
    (h : t.All (cmpLt cmp y ·)) : t.All (cmpLt cmp x ·) := h.imp fun h => H.trans h

theorem cmpLt.trans_r {cmp x y} (H : cmpLt cmp x y) {a : RBNode α}
    (h : a.All (cmpLt cmp · x)) : a.All (cmpLt cmp · y) := h.imp fun h => h.trans H

/-- The `balance1` function preserves the ordering invariants. -/
protected theorem Ordered.balance1 {l : RBNode α} {v : α} {r : RBNode α}
    (lv : l.All (cmpLt cmp · v)) (vr : r.All (cmpLt cmp v ·))
    (hl : l.Ordered cmp) (hr : r.Ordered cmp) : (balance1 l v r).Ordered cmp := by
  unfold balance1; split
  · next a x b y c =>
    have ⟨yv, _, cv⟩ := lv; have ⟨xy, yc, hx, hc⟩ := hl
    exact ⟨xy, ⟨yv, yc, yv.trans_l vr⟩, hx, cv, vr, hc, hr⟩
  · next a x b y c _ =>
    have ⟨_, _, yv, _, cv⟩ := lv; have ⟨ax, ⟨xy, xb, _⟩, ha, by_, yc, hb, hc⟩ := hl
    exact ⟨⟨xy, xy.trans_r ax, by_⟩, ⟨yv, yc, yv.trans_l vr⟩, ⟨ax, xb, ha, hb⟩, cv, vr, hc, hr⟩
  · exact ⟨lv, vr, hl, hr⟩

@[simp] theorem balance1_All {l : RBNode α} {v : α} {r : RBNode α} :
    (balance1 l v r).All p ↔ p v ∧ l.All p ∧ r.All p := by
  unfold balance1; split <;> simp [and_assoc, and_left_comm]

/-- The `balance2` function preserves the ordering invariants. -/
protected theorem Ordered.balance2 {l : RBNode α} {v : α} {r : RBNode α}
    (lv : l.All (cmpLt cmp · v)) (vr : r.All (cmpLt cmp v ·))
    (hl : l.Ordered cmp) (hr : r.Ordered cmp) : (balance2 l v r).Ordered cmp := by
  unfold balance2; split
  · next b y c z d =>
    have ⟨_, ⟨vy, vb, _⟩, _⟩ := vr; have ⟨⟨yz, _, cz⟩, zd, ⟨by_, yc, hy, hz⟩, hd⟩ := hr
    exact ⟨⟨vy, vy.trans_r lv, by_⟩, ⟨yz, yc, yz.trans_l zd⟩, ⟨lv, vb, hl, hy⟩, cz, zd, hz, hd⟩
  · next a x b y c _ =>
    have ⟨vx, va, _⟩ := vr; have ⟨ax, xy, ha, hy⟩ := hr
    exact ⟨⟨vx, vx.trans_r lv, ax⟩, xy, ⟨lv, va, hl, ha⟩, hy⟩
  · exact ⟨lv, vr, hl, hr⟩

@[simp] theorem balance2_All {l : RBNode α} {v : α} {r : RBNode α} :
    (balance2 l v r).All p ↔ p v ∧ l.All p ∧ r.All p := by
  unfold balance2; split <;> simp [and_assoc, and_left_comm]

protected theorem Ordered.setBlack {t : RBNode α} : (setBlack t).Ordered cmp ↔ t.Ordered cmp := by
  unfold setBlack; split <;> simp [Ordered]

protected theorem Balanced.setBlack : t.Balanced c n → ∃ n', (setBlack t).Balanced black n'
  | .nil => ⟨_, .nil⟩
  | .black hl hr | .red hl hr => ⟨_, hl.black hr⟩

theorem setBlack_idem {t : RBNode α} : t.setBlack.setBlack = t.setBlack := by cases t <;> rfl

theorem insert_setBlack {t : RBNode α} :
    (t.insert cmp v).setBlack = (t.ins cmp v).setBlack := by
  unfold insert; split <;> simp [setBlack_idem]

protected theorem All.ins {x : α} {t : RBNode α}
  (h₁ : p x) (h₂ : t.All p) : (ins cmp x t).All p := by
  induction t <;> unfold ins <;> simp [*] <;> split <;>
    cases ‹_=_› <;> split <;> simp at h₂ <;> simp [*]

/-- The `ins` function preserves the ordering invariants. -/
protected theorem Ordered.ins : ∀ {t : RBNode α}, t.Ordered cmp → (ins cmp x t).Ordered cmp
  | nil, _ => ⟨⟨⟩, ⟨⟩, ⟨⟩, ⟨⟩⟩
  | node red a y b, ⟨ay, yb, ha, hb⟩ => by
    unfold ins; split
    · next h => exact ⟨ay.ins ⟨h⟩, yb, ha.ins, hb⟩
    · next h => exact ⟨ay, yb.ins ⟨OrientedCmp.cmp_eq_gt.1 h⟩, ha, hb.ins⟩
    · next h => exact (⟨
        ay.imp fun ⟨h'⟩ => ⟨(TransCmp.cmp_congr_right h).trans h'⟩,
        yb.imp fun ⟨h'⟩ => ⟨(TransCmp.cmp_congr_left h).trans h'⟩, ha, hb⟩)
  | node black a y b, ⟨ay, yb, ha, hb⟩ => by
    unfold ins; split
    · next h => exact ha.ins.balance1 (ay.ins ⟨h⟩) yb hb
    · next h => exact ha.balance2 ay (yb.ins ⟨OrientedCmp.cmp_eq_gt.1 h⟩) hb.ins
    · next h => exact (⟨
        ay.imp fun ⟨h'⟩ => ⟨(TransCmp.cmp_congr_right h).trans h'⟩,
        yb.imp fun ⟨h'⟩ => ⟨(TransCmp.cmp_congr_left h).trans h'⟩, ha, hb⟩)

/-- The `insert` function preserves the ordering invariants. -/
protected theorem Ordered.insert (h : t.Ordered cmp) : (insert cmp t v).Ordered cmp := by
  unfold RBNode.insert; split <;> simp [Ordered.setBlack, h.ins (x := v)]

/--
The red-red invariant is a weakening of the red-black balance invariant which allows
the root to be red with red children, but does not allow any other violations.
It occurs as a temporary condition in the `insert` and `erase` functions.

The `p` parameter allows the `.redred` case to be dependent on an additional condition.
If it is false, then this is equivalent to the usual red-black invariant.
-/
inductive RedRed (p : Prop) : RBNode α → Nat → Prop where
  /-- A balanced tree has the red-red invariant. -/
  | balanced : Balanced t c n → RedRed p t n
  /-- A red node with balanced red children has the red-red invariant (if `p` is true). -/
  | redred : p → Balanced a c₁ n → Balanced b c₂ n → RedRed p (node red a x b) n

/-- When `p` is false, the red-red case is impossible so the tree is balanced. -/
protected theorem RedRed.of_false (h : ¬p) : RedRed p t n → ∃ c, Balanced t c n
  | .balanced h => ⟨_, h⟩
  | .redred hp .. => nomatch h hp

/-- A `red` node with the red-red invariant has balanced children. -/
protected theorem RedRed.of_red : RedRed p (node red a x b) n →
    ∃ c₁ c₂, Balanced a c₁ n ∧ Balanced b c₂ n
  | .balanced (.red ha hb) | .redred _ ha hb => ⟨_, _, ha, hb⟩

/-- The red-red invariant is monotonic in `p`. -/
protected theorem RedRed.imp (h : p → q) : RedRed p t n → RedRed q t n
  | .balanced h => .balanced h
  | .redred hp ha hb => .redred (h hp) ha hb

/-- If `t` has the red-red invariant, then setting the root to black yields a balanced tree. -/
protected theorem RedRed.setBlack : t.RedRed p n → ∃ n', (setBlack t).Balanced black n'
  | .balanced h => h.setBlack
  | .redred _ hl hr => ⟨_, hl.black hr⟩

/-- The `balance1` function repairs the balance invariant when the first argument is red-red. -/
protected theorem RedRed.balance1 {l : RBNode α} {v : α} {r : RBNode α}
    (hl : l.RedRed p n) (hr : r.Balanced c n) : ∃ c, (balance1 l v r).Balanced c (n + 1) := by
  unfold balance1; split
  · have .redred _ (.red ha hb) hc := hl; exact ⟨_, .red (.black ha hb) (.black hc hr)⟩
  · have .redred _ ha (.red hb hc) := hl; exact ⟨_, .red (.black ha hb) (.black hc hr)⟩
  · next H1 H2 => match hl with
    | .balanced hl => exact ⟨_, .black hl hr⟩
    | .redred _ (c₁ := black) (c₂ := black) ha hb => exact ⟨_, .black (.red ha hb) hr⟩
    | .redred _ (c₁ := red) (.red ..) _ => cases H1 _ _ _ _ _ rfl
    | .redred _ (c₂ := red) _ (.red ..) => cases H2 _ _ _ _ _ rfl

/-- The `balance2` function repairs the balance invariant when the second argument is red-red. -/
protected theorem RedRed.balance2 {l : RBNode α} {v : α} {r : RBNode α}
    (hl : l.Balanced c n) (hr : r.RedRed p n) : ∃ c, (balance2 l v r).Balanced c (n + 1) := by
  unfold balance2; split
  · have .redred _ (.red ha hb) hc := hr; exact ⟨_, .red (.black hl ha) (.black hb hc)⟩
  · have .redred _ ha (.red hb hc) := hr; exact ⟨_, .red (.black hl ha) (.black hb hc)⟩
  · next H1 H2 => match hr with
    | .balanced hr => exact ⟨_, .black hl hr⟩
    | .redred _ (c₁ := black) (c₂ := black) ha hb => exact ⟨_, .black hl (.red ha hb)⟩
    | .redred _ (c₁ := red) (.red ..) _ => cases H1 _ _ _ _ _ rfl
    | .redred _ (c₂ := red) _ (.red ..) => cases H2 _ _ _ _ _ rfl

/-- The `balance1` function does nothing if the first argument is already balanced. -/
theorem balance1_eq {l : RBNode α} {v : α} {r : RBNode α}
    (hl : l.Balanced c n) : balance1 l v r = node black l v r := by
  unfold balance1; split <;> first | rfl | match hl with.

/-- The `balance2` function does nothing if the second argument is already balanced. -/
theorem balance2_eq {l : RBNode α} {v : α} {r : RBNode α}
    (hr : r.Balanced c n) : balance2 l v r = node black l v r := by
  unfold balance2; split <;> first | rfl | match hr with.

/-! ## insert -/

/--
The balance invariant of the `ins` function.
The result of inserting into the tree either yields a balanced tree,
or a tree which is almost balanced except that it has a red-red violation at the root.
-/
protected theorem Balanced.ins (cmp v) {t : RBNode α}
    (h : t.Balanced c n) : (ins cmp v t).RedRed (t.isRed = red) n := by
  induction h with
  | nil => exact .balanced (.red .nil .nil)
  | @red a n b x hl hr ihl ihr =>
    unfold ins; split
    · match ins cmp v a, ihl with
      | _, .balanced .nil => exact .balanced (.red .nil hr)
      | _, .balanced (.red ha hb) => exact .redred rfl (.red ha hb) hr
      | _, .balanced (.black ha hb) => exact .balanced (.red (.black ha hb) hr)
      | _, .redred h .. => cases hl <;> cases h
    · match ins cmp v b, ihr with
      | _, .balanced .nil => exact .balanced (.red hl .nil)
      | _, .balanced (.red ha hb) => exact .redred rfl hl (.red ha hb)
      | _, .balanced (.black ha hb) => exact .balanced (.red hl (.black ha hb))
      | _, .redred h .. => cases hr <;> cases h
    · exact .balanced (.red hl hr)
  | @black a ca n b cb x hl hr ihl ihr =>
    unfold ins; split
    · exact have ⟨c, h⟩ := ihl.balance1 hr; .balanced h
    · exact have ⟨c, h⟩ := ihr.balance2 hl; .balanced h
    · exact .balanced (.black hl hr)

/--
The `insert` function is balanced if the input is balanced.
(We lose track of both the color and the black-height of the result,
so this is only suitable for use on the root of the tree.)
-/
theorem Balanced.insert {t : RBNode α} (h : t.Balanced c n) :
    ∃ c' n', (insert cmp t v).Balanced c' n' := by
  unfold insert; match ins cmp v t, h.ins cmp v with
  | _, .balanced h => split <;> [exact ⟨_, h.setBlack⟩, exact ⟨_, _, h⟩]
  | _, .redred _ ha hb => have .node red .. := t; exact ⟨_, _, .black ha hb⟩

protected theorem All.setRed {t : RBNode α} (h : t.All p) : (setRed t).All p := by
  unfold setRed; split <;> simp_all

/-- The `setRed` function preserves the ordering invariants. -/
protected theorem Ordered.setRed {t : RBNode α} : (setRed t).Ordered cmp ↔ t.Ordered cmp := by
  unfold setRed; split <;> simp [Ordered]

protected theorem All.balLeft
    (hl : l.All p) (hv : p v) (hr : r.All p) : (balLeft l v r).All p := by
  unfold balLeft; split <;> simp_all; split <;> simp_all [All.setRed]

/-- The `balLeft` function preserves the ordering invariants. -/
protected theorem Ordered.balLeft {l : RBNode α} {v : α} {r : RBNode α}
    (lv : l.All (cmpLt cmp · v)) (vr : r.All (cmpLt cmp v ·))
    (hl : l.Ordered cmp) (hr : r.Ordered cmp) : (balLeft l v r).Ordered cmp := by
  unfold balLeft; split
  · exact ⟨lv, vr, hl, hr⟩
  split
  · exact hl.balance2 lv vr hr
  · have ⟨vy, va, _⟩ := vr.2.1; have ⟨⟨yz, _, bz⟩, zc, ⟨ay, yb, ha, hb⟩, hc⟩ := hr
    exact ⟨⟨vy, vy.trans_r lv, ay⟩, balance2_All.2 ⟨yz, yb, (yz.trans_l zc).setRed⟩,
      ⟨lv, va, hl, ha⟩, hb.balance2 bz zc.setRed (Ordered.setRed.2 hc)⟩
  · exact ⟨lv, vr, hl, hr⟩

/-- The balancing properties of the `balLeft` function. -/
protected theorem Balanced.balLeft (hl : l.RedRed True n) (hr : r.Balanced cr (n + 1)) :
    (balLeft l v r).RedRed (cr = red) (n + 1) := by
  unfold balLeft; split
  · next a x b => exact
    let ⟨ca, cb, ha, hb⟩ := hl.of_red
    match cr with
    | red => .redred rfl (.black ha hb) hr
    | black => .balanced (.red (.black ha hb) hr)
  · next H => exact match hl with
    | .redred .. => nomatch H _ _ _ rfl
    | .balanced hl => match hr with
      | .black ha hb =>
        let ⟨c, h⟩ := RedRed.balance2 hl (.redred trivial ha hb); .balanced h
      | .red (.black ha hb) (.black hc hd) =>
        let ⟨c, h⟩ := RedRed.balance2 hb (.redred trivial hc hd); .redred rfl (.black hl ha) h

protected theorem All.balRight
    (hl : l.All p) (hv : p v) (hr : r.All p) : (balRight l v r).All p := by
  unfold balRight; split <;> simp_all; split <;> simp_all [All.setRed]

/-- The `balRight` function preserves the ordering invariants. -/
protected theorem Ordered.balRight {l : RBNode α} {v : α} {r : RBNode α}
    (lv : l.All (cmpLt cmp · v)) (vr : r.All (cmpLt cmp v ·))
    (hl : l.Ordered cmp) (hr : r.Ordered cmp) : (balRight l v r).Ordered cmp := by
  unfold balRight; split
  · exact ⟨lv, vr, hl, hr⟩
  split
  · exact hl.balance1 lv vr hr
  · have ⟨yv, _, cv⟩ := lv.2.2; have ⟨ax, ⟨xy, xb, _⟩, ha, by_, yc, hb, hc⟩ := hl
    exact ⟨balance1_All.2 ⟨xy, (xy.trans_r ax).setRed, by_⟩, ⟨yv, yc, yv.trans_l vr⟩,
      (Ordered.setRed.2 ha).balance1 ax.setRed xb hb, cv, vr, hc, hr⟩
  · exact ⟨lv, vr, hl, hr⟩

/-- The balancing properties of the `balRight` function. -/
protected theorem Balanced.balRight (hl : l.Balanced cl (n + 1)) (hr : r.RedRed True n) :
    (balRight l v r).RedRed (cl = red) (n + 1) := by
  unfold balRight; split
  · next b y c => exact
    let ⟨cb, cc, hb, hc⟩ := hr.of_red
    match cl with
    | red => .redred rfl hl (.black hb hc)
    | black => .balanced (.red hl (.black hb hc))
  · next H => exact match hr with
    | .redred .. => nomatch H _ _ _ rfl
    | .balanced hr => match hl with
      | .black hb hc =>
        let ⟨c, h⟩ := RedRed.balance1 (.redred trivial hb hc) hr; .balanced h
      | .red (.black ha hb) (.black hc hd) =>
        let ⟨c, h⟩ := RedRed.balance1 (.redred trivial ha hb) hc; .redred rfl h (.black hd hr)

protected theorem All.append (hl : l.All p) (hr : r.All p) : (append l r).All p := by
  unfold append; split <;> simp [*]
  · have ⟨hx, ha, hb⟩ := hl; have ⟨hy, hc, hd⟩ := hr
    have := hb.append hc; split <;> simp_all
  · have ⟨hx, ha, hb⟩ := hl; have ⟨hy, hc, hd⟩ := hr
    have := hb.append hc; split <;> simp_all [All.balLeft]
  · simp_all [hl.append hr.2.1]
  · simp_all [hl.2.2.append hr]
termination_by _ => l.size + r.size

/-- The `append` function preserves the ordering invariants. -/
protected theorem Ordered.append {l : RBNode α} {v : α} {r : RBNode α}
    (lv : l.All (cmpLt cmp · v)) (vr : r.All (cmpLt cmp v ·))
    (hl : l.Ordered cmp) (hr : r.Ordered cmp) : (append l r).Ordered cmp := by
  unfold append; split
  · exact hr
  · exact hl
  · have ⟨xv, _, bv⟩ := lv; have ⟨ax, xb, ha, hb⟩ := hl
    have ⟨vy, vc, _⟩ := vr; have ⟨cy, yd, hc, hd⟩ := hr
    have : _ ∧ _ ∧ _ := ⟨hb.append bv vc hc, xb.append (xv.trans_l vc), (vy.trans_r bv).append cy⟩
    split
    · next H =>
      have ⟨⟨b'z, c'z, hb', hc'⟩, ⟨xz, xb', _⟩, zy, _, c'y⟩ := H ▸ this
      have az := xz.trans_r ax; have zd := zy.trans_l yd
      exact ⟨⟨xz, az, b'z⟩, ⟨zy, c'z, zd⟩, ⟨ax, xb', ha, hb'⟩, c'y, yd, hc', hd⟩
    · have ⟨hbc, xbc, bcy⟩ := this; have xy := xv.trans vy
      exact ⟨ax, ⟨xy, xbc, xy.trans_l yd⟩, ha, bcy, yd, hbc, hd⟩
  · have ⟨xv, _, bv⟩ := lv; have ⟨ax, xb, ha, hb⟩ := hl
    have ⟨vy, vc, _⟩ := vr; have ⟨cy, yd, hc, hd⟩ := hr
    have : _ ∧ _ ∧ _ := ⟨hb.append bv vc hc, xb.append (xv.trans_l vc), (vy.trans_r bv).append cy⟩
    split
    · next H =>
      have ⟨⟨b'z, c'z, hb', hc'⟩, ⟨xz, xb', _⟩, zy, _, c'y⟩ := H ▸ this
      have az := xz.trans_r ax; have zd := zy.trans_l yd
      exact ⟨⟨xz, az, b'z⟩, ⟨zy, c'z, zd⟩, ⟨ax, xb', ha, hb'⟩, c'y, yd, hc', hd⟩
    · have ⟨hbc, xbc, bcy⟩ := this; have xy := xv.trans vy
      exact ha.balLeft ax ⟨xy, xbc, xy.trans_l yd⟩ ⟨bcy, yd, hbc, hd⟩
  · have ⟨vx, vb, _⟩ := vr; have ⟨bx, yc, hb, hc⟩ := hr
    exact ⟨(vx.trans_r lv).append bx, yc, hl.append lv vb hb, hc⟩
  · have ⟨xv, _, bv⟩ := lv; have ⟨ax, xb, ha, hb⟩ := hl
    exact ⟨ax, xb.append (xv.trans_l vr), ha, hb.append bv vr hr⟩
termination_by _ => l.size + r.size

/-- The balance properties of the `append` function. -/
protected theorem Balanced.append {l r : RBNode α}
    (hl : l.Balanced c₁ n) (hr : r.Balanced c₂ n) :
    (l.append r).RedRed (c₁ = black → c₂ ≠ black) n := by
  unfold append; split
  · exact .balanced hr
  · exact .balanced hl
  · next b c _ _ =>
    have .red ha hb := hl; have .red hc hd := hr
    have ⟨_, IH⟩ := (hb.append hc).of_false (· rfl rfl); split
    · next e =>
      have .red hb' hc' := e ▸ IH
      exact .redred (fun.) (.red ha hb') (.red hc' hd)
    · next bcc _ H =>
      match bcc, append b c, IH, H with
      | black, _, IH, _ => exact .redred (fun.) ha (.red IH hd)
      | red, _, .red .., H => cases H _ _ _ rfl
  · next b c _ _ =>
    have .black ha hb := hl; have .black hc hd := hr
    have IH := hb.append hc; split
    · next e => match e ▸ IH with
      | .balanced (.red hb' hc') | .redred _ hb' hc' =>
        exact .balanced (.red (.black ha hb') (.black hc' hd))
    · next H =>
      match append b c, IH, H with
      | bc, .balanced hbc, _ =>
        unfold balLeft; split
        · have .red ha' hb' := ha
          exact .balanced (.red (.black ha' hb') (.black hbc hd))
        · exact have ⟨c, h⟩ := RedRed.balance2 ha (.redred trivial hbc hd); .balanced h
      | _, .redred .., H => cases H _ _ _ rfl
  · have .red hc hd := hr; have IH := hl.append hc
    have .black ha hb := hl; have ⟨c, IH⟩ := IH.of_false (· rfl rfl)
    exact .redred (fun.) IH hd
  · have .red ha hb := hl; have IH := hb.append hr
    have .black hc hd := hr; have ⟨c, IH⟩ := IH.of_false (· rfl rfl)
    exact .redred (fun.) ha IH
termination_by _ => l.size + r.size

/-! ## erase -/

/--
The invariant of the `del` function.
* If the input tree is black, then the result of deletion is a red-red tree with
  black-height lowered by 1.
* If the input tree is red or nil, then the result of deletion is a balanced tree with
  some color and the same black-height.
-/
def DelProp (p : RBColor) (t : RBNode α) (n : Nat) : Prop :=
  match p with
  | black => ∃ n', n = n' + 1 ∧ RedRed True t n'
  | red => ∃ c, Balanced t c n

/-- The `DelProp` property is a strengthened version of the red-red invariant. -/
theorem DelProp.redred (h : DelProp c t n) : ∃ n', RedRed (c = black) t n' := by
  unfold DelProp at h
  exact match c, h with
  | red, ⟨_, h⟩ => ⟨_, .balanced h⟩
  | black, ⟨_, _, h⟩ => ⟨_, h.imp fun _ => rfl⟩

protected theorem All.del : ∀ {t : RBNode α}, t.All p → (del cut t).All p
  | .nil, h => h
  | .node .., ⟨hy, ha, hb⟩ => by
    unfold del; split
    · split
      · exact ha.del.balLeft hy hb
      · exact ⟨hy, ha.del, hb⟩
    · split
      · exact ha.balRight hy hb.del
      · exact ⟨hy, ha, hb.del⟩
    · exact ha.append hb

/-- The `del` function preserves the ordering invariants. -/
protected theorem Ordered.del : ∀ {t : RBNode α}, t.Ordered cmp → (del cut t).Ordered cmp
  | .nil, _ => ⟨⟩
  | .node _ a y b, ⟨ay, yb, ha, hb⟩ => by
    unfold del; split
    · split
      · exact ha.del.balLeft ay.del yb hb
      · exact ⟨ay.del, yb, ha.del, hb⟩
    · split
      · exact ha.balRight ay yb.del hb.del
      · exact ⟨ay, yb.del, ha, hb.del⟩
    · exact ha.append ay yb hb

/-- The `del` function has the `DelProp` property. -/
protected theorem Balanced.del {t : RBNode α} (h : t.Balanced c n) :
    (t.del cut).DelProp t.isBlack n := by
  induction h with
  | nil => exact ⟨_, .nil⟩
  | @black a _ n b _ _ ha hb iha ihb =>
    refine ⟨_, rfl, ?_⟩
    unfold del; split
    · exact match a, n, iha with
      | .nil, _, ⟨c, ha⟩ | .node red .., _, ⟨c, ha⟩ => .redred ⟨⟩ ha hb
      | .node black .., _, ⟨n, rfl, ha⟩ => (hb.balLeft ha).imp fun _ => ⟨⟩
    · exact match b, n, ihb with
      | .nil, _, ⟨c, hb⟩ | .node .red .., _, ⟨c, hb⟩ => .redred ⟨⟩ ha hb
      | .node black .., _, ⟨n, rfl, hb⟩ => (ha.balRight hb).imp fun _ => ⟨⟩
    · exact (ha.append hb).imp fun _ => ⟨⟩
  | @red a n b _ ha hb iha ihb =>
    unfold del; split
    · exact match a, n, iha with
      | .nil, _, _ => ⟨_, .red ha hb⟩
      | .node black .., _, ⟨n, rfl, ha⟩ => (hb.balLeft ha).of_false (fun.)
    · exact match b, n, ihb with
      | .nil, _, _ => ⟨_, .red ha hb⟩
      | .node black .., _, ⟨n, rfl, hb⟩ => (ha.balRight hb).of_false (fun.)
    · exact (ha.append hb).of_false (· rfl rfl)

/-- The `erase` function preserves the ordering invariants. -/
protected theorem Ordered.erase {t : RBNode α} (h : t.Ordered cmp) : (erase cut t).Ordered cmp :=
  Ordered.setBlack.2 h.del

/-- The `erase` function preserves the balance invariants. -/
protected theorem Balanced.erase {t : RBNode α}
    (h : t.Balanced c n) : ∃ n, (t.erase cut).Balanced black n :=
  have ⟨_, h⟩ := h.del.redred; h.setBlack

/-! ## path well-formedness -/

/--
The property of a tree returned by `t.zoom cut`.
It is either empty, or has a node satisfying `cut` at the root.
-/
def Zoomed (cut : α → Ordering) : RBNode α → Prop
  | nil => True
  | node _ _ x _ => cut x = .eq

/--
Auxiliary definition for `zoom_ins`: set the root of the tree to `v`, creating a node if necessary.
-/
def setRoot (v : α) : RBNode α → RBNode α
  | nil => node red nil v nil
  | node c a _ b => node c a v b

/--
Auxiliary definition for `zoom_ins`: set the root of the tree to `v`, creating a node if necessary.
-/
def delRoot : RBNode α → RBNode α
  | nil => nil
  | node _ a _ b => a.append b

namespace Path

/-- Same as `fill` but taking its arguments in a pair for easier composition with `zoom`. -/
@[inline] def fill' : RBNode α × Path α → RBNode α := fun (t, path) => path.fill t

theorem zoom_fill' (cut : α → Ordering) (t : RBNode α) (path : Path α) :
    fill' (zoom cut t path) = path.fill t := by
  induction t generalizing path with
  | nil => rfl
  | node _ _ _ _ iha ihb => unfold zoom; split <;> [apply iha, apply ihb, rfl]

theorem zoom_fill (H : zoom cut t path = (t', path')) : path.fill t = path'.fill t' :=
  (H ▸ zoom_fill' cut t path).symm

theorem zoom_zoomed (H : zoom cut t path = (t', path')) : t'.Zoomed cut :=
  match t, H with
  | nil, rfl => trivial
  | node .., e => by
    revert e; unfold zoom; split
    · exact zoom_zoomed
    · exact zoom_zoomed
    · next H => intro e; cases e; exact H

theorem zoom_ins {t : RBNode α} {cmp : α → α → Ordering} :
    t.zoom (cmp v) path = (t', path') →
    path.ins (t.ins cmp v) = path'.ins (t'.setRoot v) := by
  unfold RBNode.ins; split <;> simp [zoom]
  · intro | rfl, rfl => rfl
  all_goals
  · split
    · exact zoom_ins
    · exact zoom_ins
    · intro | rfl => rfl

theorem insertNew_eq_insert (h : zoom (cmp v) t = (nil, path)) :
    path.insertNew v = (t.insert cmp v).setBlack :=
  insert_setBlack .. ▸ (zoom_ins h).symm

theorem zoom_del {t : RBNode α} :
    t.zoom cut path = (t', path') →
    path.del (t.del cut) (match t with | node c .. => c | _ => red) =
    path'.del t'.delRoot (match t' with | node c .. => c | _ => red) := by
  unfold RBNode.del; split <;> simp [zoom]
  · intro | rfl, rfl => rfl
  · next c a y b =>
    split
    · have IH := @zoom_del (t := a)
      match a with
      | nil => intro | rfl => rfl
      | node black .. | node red .. => apply IH
    · have IH := @zoom_del (t := b)
      match b with
      | nil => intro | rfl => rfl
      | node black .. | node red .. => apply IH
    · intro | rfl => rfl

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

protected theorem _root_.Std.RBNode.Balanced.zoom : t.Balanced c n → path.Balanced c₀ n₀ c n →
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

theorem ins_eq_fill {path : Path α} {t : RBNode α} :
    path.Balanced c₀ n₀ c n → t.Balanced c n → path.ins t = (path.fill t).setBlack
  | .root, h => rfl
  | .redL hb H, ha | .redR ha H, hb => by unfold ins; exact ins_eq_fill H (.red ha hb)
  | .blackL hb H, ha => by rw [ins, fill, ← ins_eq_fill H (.black ha hb), balance1_eq ha]
  | .blackR ha H, hb => by rw [ins, fill, ← ins_eq_fill H (.black ha hb), balance2_eq hb]

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
  | blackL hr hp ih => exact have ⟨c, h⟩ := ht.balance1 hr; ih (.balanced h)
  | blackR hl hp ih => exact have ⟨c, h⟩ := ht.balance2 hl; ih (.balanced h)

protected theorem Balanced.insertNew {path : Path α} (H : path.Balanced c n black 0) :
    ∃ n, (path.insertNew v).Balanced black n := H.ins (.balanced (.red .nil .nil))

protected theorem Balanced.insert {path : Path α} (hp : path.Balanced c₀ n₀ c n) :
    t.Balanced c n → ∃ c n, (path.insert t v).Balanced c n
  | .nil => ⟨_, hp.insertNew⟩
  | .red ha hb => ⟨_, _, hp.fill (.red ha hb)⟩
  | .black ha hb => ⟨_, _, hp.fill (.black ha hb)⟩

theorem zoom_insert {path : Path α} {t : RBNode α} (ht : t.Balanced c n)
    (H : zoom (cmp v) t = (t', path)) :
    (path.insert t' v).setBlack = (t.insert cmp v).setBlack := by
  have ⟨_, _, ht', hp'⟩ := ht.zoom .root H
  cases ht' with simp [insert]
  | nil => simp [insertNew_eq_insert H, setBlack_idem]
  | red hl hr => rw [← ins_eq_fill hp' (.red hl hr), insert_setBlack]; exact (zoom_ins H).symm
  | black hl hr => rw [← ins_eq_fill hp' (.black hl hr), insert_setBlack]; exact (zoom_ins H).symm

protected theorem Balanced.del {path : Path α}
    (hp : path.Balanced c₀ n₀ c n) (ht : t.DelProp c' n) (hc : c = black → c' ≠ red) :
    ∃ n, (path.del t c').Balanced black n := by
  induction hp generalizing t c' with
  | root => match c', ht with
    | red, ⟨_, h⟩ | black, ⟨_, _, h⟩ => exact h.setBlack
  | @redL _ n _ _ hb hp ih => match c', n, ht with
    | red, _, _ => cases hc rfl rfl
    | black, _, ⟨_, rfl, ha⟩ => exact ih ((hb.balLeft ha).of_false (fun.)) (fun.)
  | @redR _ n _ _ ha hp ih => match c', n, ht with
    | red, _, _ => cases hc rfl rfl
    | black, _, ⟨_, rfl, hb⟩ => exact ih ((ha.balRight hb).of_false (fun.)) (fun.)
  | @blackL _ _ n _ _ _ hb hp ih => match c', n, ht with
    | red, _, ⟨_, ha⟩ => exact ih ⟨_, rfl, .redred ⟨⟩ ha hb⟩ (fun.)
    | black, _, ⟨_, rfl, ha⟩ => exact ih ⟨_, rfl, (hb.balLeft ha).imp fun _ => ⟨⟩⟩ (fun.)
  | @blackR _ _ n _ _ _ ha hp ih =>  match c', n, ht with
    | red, _, ⟨_, hb⟩ => exact ih ⟨_, rfl, .redred ⟨⟩ ha hb⟩ (fun.)
    | black, _, ⟨_, rfl, hb⟩ => exact ih ⟨_, rfl, (ha.balRight hb).imp fun _ => ⟨⟩⟩ (fun.)

end Path

/-! ## alter -/

-- /-- The `alter` function preserves the ordering invariants. -/
-- protected theorem Ordered.alter {t : RBNode α}
--     (H : ∀ {x y}, t.find? cut = some x → f (some x) = some y → cmpEq cmp y x)
--     (h : t.Ordered cmp) : (alter cut f t).Ordered cmp :=
--   sorry

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
      | .red ha hb => exact ⟨_, hp.del ((ha.append hb).of_false (· rfl rfl)) (fun.)⟩
      | .black ha hb => exact ⟨_, hp.del ⟨_, rfl, (ha.append hb).imp fun _ => ⟨⟩⟩ (fun.)⟩
    · match h with
      | .red ha hb => exact ⟨_, _, hp.fill (.red ha hb)⟩
      | .black ha hb => exact ⟨_, _, hp.fill (.black ha hb)⟩

/-- The well-formedness invariant implies the ordering and balance properties. -/
theorem WF.out {t : RBNode α} (h : t.WF cmp) : t.Ordered cmp ∧ ∃ c n, t.Balanced c n := by
  induction h with
  | mk o h => exact ⟨o, _, _, h⟩
  | insert _ ih => have ⟨o, _, _, h⟩ := ih; exact ⟨o.insert, h.insert⟩
  | erase _ ih => have ⟨o, _, _, h⟩ := ih; exact ⟨o.erase, _, h.erase⟩
  -- | alter hf _ ih => have ⟨o, _, _, h⟩ := ih; exact ⟨o.alter hf, h.alter⟩

/--
The well-formedness invariant for a red-black tree is exactly the `mk` constructor,
because the other constructors of `WF` are redundant.
-/
@[simp] theorem WF_iff {t : RBNode α} : t.WF cmp ↔ t.Ordered cmp ∧ ∃ c n, t.Balanced c n :=
  ⟨fun h => h.out, fun ⟨o, _, _, h⟩ => .mk o h⟩

/-- The `map` function preserves the balance invariants. -/
protected theorem Balanced.map {t : RBNode α} : t.Balanced c n → (t.map f).Balanced c n
  | .nil => .nil
  | .red hl hr => .red hl.map hr.map
  | .black hl hr => .black hl.map hr.map

/-- The property of a map function `f` which ensures the `map` operation is valid. -/
class IsMonotone (cmpα cmpβ) (f : α → β) : Prop where
  /-- If `x < y` then `f x < f y`. -/
  lt_mono : cmpLt cmpα x y → cmpLt cmpβ (f x) (f y)

/-- Sufficient condition for `map` to preserve an `All` quantifier. -/
protected theorem All.map {f : α → β} (H : ∀ {x}, p x → q (f x)) :
    ∀ {t : RBNode α}, t.All p → (t.map f).All q
  | nil, _ => ⟨⟩
  | node .., ⟨hx, ha, hb⟩ => ⟨H hx, ha.map H, hb.map H⟩

/-- The `map` function preserves the order invariants if `f` is monotone. -/
protected theorem Ordered.map (f : α → β) [IsMonotone cmpα cmpβ f] :
    ∀ {t : RBNode α}, t.Ordered cmpα → (t.map f).Ordered cmpβ
  | nil, _ => ⟨⟩
  | node _ a x b, ⟨ax, xb, ha, hb⟩ => by
    refine ⟨ax.map ?_, xb.map ?_, ha.map f, hb.map f⟩ <;> exact IsMonotone.lt_mono

end RBNode

namespace RBSet
export RBNode (IsMonotone)

/--
`O(n)`. Map a function on every value in the tree.
This requires `IsMonotone` on the function in order to preserve the order invariant.
-/
@[inline] def map (f : α → β) [IsMonotone cmpα cmpβ f] (t : RBSet α cmpα) : RBSet β cmpβ :=
  ⟨t.1.map f, have ⟨h₁, _, _, h₂⟩ := t.2.out; .mk (h₁.map _) h₂.map⟩

end RBSet

namespace RBMap
export RBNode (IsMonotone)

namespace Imp

/--
Applies `f` to the second component.
We extract this as a function so that `IsMonotone (mapSnd f)` can be an instance.
-/
@[inline] def mapSnd (f : α → β → γ) := fun (a, b) => (a, f a b)

instance (cmp : α → α → Ordering) (f : α → β → γ) :
    IsMonotone (byKey Prod.fst cmp) (byKey Prod.fst cmp) (mapSnd f) where
  lt_mono | ⟨h⟩ => ⟨@fun _ => @h {
    symm := fun (a₁, b₁) (a₂, b₂) =>
      OrientedCmp.symm (cmp := byKey Prod.fst cmp) (a₁, f a₁ b₁) (a₂, f a₂ b₂)
    le_trans := @fun (a₁, b₁) (a₂, b₂) (a₃, b₃) =>
      TransCmp.le_trans (cmp := byKey Prod.fst cmp)
        (x := (a₁, f a₁ b₁)) (y := (a₂, f a₂ b₂)) (z := (a₃, f a₃ b₃))
  }⟩

end Imp

/-- `O(n)`. Map a function on the values in the map. -/
def mapVal (f : α → β → γ) (t : RBMap α β cmp) : RBMap α γ cmp := t.map (Imp.mapSnd f)

end RBMap
