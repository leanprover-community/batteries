/-
Copyright (c) 2022 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Batteries.Data.RBMap.Basic
import Batteries.Tactic.SeqFocus

/-!
# Lemmas for Red-black trees

The main theorem in this file is `WF_def`, which shows that the `RBNode.WF.mk` constructor
subsumes the others, by showing that `insert` and `erase` satisfy the red-black invariants.
-/

namespace Batteries

namespace RBNode
open RBColor

attribute [simp] All

theorem All.trivial (H : ∀ {x : α}, p x) : ∀ {t : RBNode α}, t.All p
  | nil => _root_.trivial
  | node .. => ⟨H, All.trivial H, All.trivial H⟩

theorem All_and {t : RBNode α} : t.All (fun a => p a ∧ q a) ↔ t.All p ∧ t.All q := by
  induction t <;> simp [*, and_assoc, and_left_comm]

protected theorem cmpLT.flip (h₁ : cmpLT cmp x y) : cmpLT (flip cmp) y x :=
  ⟨have : TransCmp cmp := inferInstanceAs (TransCmp (flip (flip cmp))); h₁.1⟩

theorem cmpLT.trans (h₁ : cmpLT cmp x y) (h₂ : cmpLT cmp y z) : cmpLT cmp x z :=
  ⟨TransCmp.lt_trans h₁.1 h₂.1⟩

theorem cmpLT.trans_l {cmp x y} (H : cmpLT cmp x y) {t : RBNode α}
    (h : t.All (cmpLT cmp y ·)) : t.All (cmpLT cmp x ·) := h.imp fun h => H.trans h

theorem cmpLT.trans_r {cmp x y} (H : cmpLT cmp x y) {a : RBNode α}
    (h : a.All (cmpLT cmp · x)) : a.All (cmpLT cmp · y) := h.imp fun h => h.trans H

theorem cmpEq.lt_congr_left (H : cmpEq cmp x y) : cmpLT cmp x z ↔ cmpLT cmp y z :=
  ⟨fun ⟨h⟩ => ⟨TransCmp.cmp_congr_left H.1 ▸ h⟩, fun ⟨h⟩ => ⟨TransCmp.cmp_congr_left H.1 ▸ h⟩⟩

theorem cmpEq.lt_congr_right (H : cmpEq cmp y z) : cmpLT cmp x y ↔ cmpLT cmp x z :=
  ⟨fun ⟨h⟩ => ⟨TransCmp.cmp_congr_right H.1 ▸ h⟩, fun ⟨h⟩ => ⟨TransCmp.cmp_congr_right H.1 ▸ h⟩⟩

@[simp] theorem reverse_reverse (t : RBNode α) : t.reverse.reverse = t := by
  induction t <;> simp [*]

theorem reverse_eq_iff {t t' : RBNode α} : t.reverse = t' ↔ t = t'.reverse := by
  constructor <;> rintro rfl <;> simp

@[simp] theorem reverse_balance1 (l : RBNode α) (v : α) (r : RBNode α) :
    (balance1 l v r).reverse = balance2 r.reverse v l.reverse := by
  unfold balance1 balance2; split <;> simp
  · rw [balance2.match_1.eq_2]; simp [reverse_eq_iff]; intros; solve_by_elim
  · rw [balance2.match_1.eq_3] <;> (simp [reverse_eq_iff]; intros; solve_by_elim)

@[simp] theorem reverse_balance2 (l : RBNode α) (v : α) (r : RBNode α) :
    (balance2 l v r).reverse = balance1 r.reverse v l.reverse := by
  refine Eq.trans ?_ (reverse_reverse _); rw [reverse_balance1]; simp

@[simp] theorem All.reverse {t : RBNode α} : t.reverse.All p ↔ t.All p := by
  induction t <;> simp [*, and_comm]

/-- The `reverse` function reverses the ordering invariants. -/
protected theorem Ordered.reverse : ∀ {t : RBNode α}, t.Ordered cmp → t.reverse.Ordered (flip cmp)
  | .nil, _ => ⟨⟩
  | .node .., ⟨lv, vr, hl, hr⟩ =>
    ⟨(All.reverse.2 vr).imp cmpLT.flip, (All.reverse.2 lv).imp cmpLT.flip, hr.reverse, hl.reverse⟩

protected theorem Balanced.reverse {t : RBNode α} : t.Balanced c n → t.reverse.Balanced c n
  | .nil => .nil
  | .black hl hr => .black hr.reverse hl.reverse
  | .red hl hr => .red hr.reverse hl.reverse

/-- The `balance1` function preserves the ordering invariants. -/
protected theorem Ordered.balance1 {l : RBNode α} {v : α} {r : RBNode α}
    (lv : l.All (cmpLT cmp · v)) (vr : r.All (cmpLT cmp v ·))
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
    (lv : l.All (cmpLT cmp · v)) (vr : r.All (cmpLT cmp v ·))
    (hl : l.Ordered cmp) (hr : r.Ordered cmp) : (balance2 l v r).Ordered cmp := by
  rw [← reverse_reverse (balance2 ..), reverse_balance2]
  exact .reverse <| hr.reverse.balance1
    ((All.reverse.2 vr).imp cmpLT.flip) ((All.reverse.2 lv).imp cmpLT.flip) hl.reverse

@[simp] theorem balance2_All {l : RBNode α} {v : α} {r : RBNode α} :
    (balance2 l v r).All p ↔ p v ∧ l.All p ∧ r.All p := by
  unfold balance2; split <;> simp [and_assoc, and_left_comm]

@[simp] theorem reverse_setBlack {t : RBNode α} : (setBlack t).reverse = setBlack t.reverse := by
  unfold setBlack; split <;> simp

protected theorem Ordered.setBlack {t : RBNode α} : (setBlack t).Ordered cmp ↔ t.Ordered cmp := by
  unfold setBlack; split <;> simp [Ordered]

protected theorem Balanced.setBlack : t.Balanced c n → ∃ n', (setBlack t).Balanced black n'
  | .nil => ⟨_, .nil⟩
  | .black hl hr | .red hl hr => ⟨_, hl.black hr⟩

theorem setBlack_idem {t : RBNode α} : t.setBlack.setBlack = t.setBlack := by cases t <;> rfl

@[simp] theorem reverse_ins [inst : @OrientedCmp α cmp] {t : RBNode α} :
    (ins cmp x t).reverse = ins (flip cmp) x t.reverse := by
  induction t <;> [skip; (rename_i c a y b iha ihb; cases c)] <;> simp [ins, flip]
    <;> rw [← inst.symm x y] <;> split <;> simp [*, Ordering.swap, iha, ihb]

protected theorem All.ins {x : α} {t : RBNode α}
  (h₁ : p x) (h₂ : t.All p) : (ins cmp x t).All p := by
  induction t <;> unfold ins <;> try simp [*]
  split <;> cases ‹_=_› <;> split <;> simp at h₂ <;> simp [*]

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

@[simp] theorem isRed_reverse {t : RBNode α} : t.reverse.isRed = t.isRed := by
  cases t <;> simp [isRed]

@[simp] theorem reverse_insert [inst : @OrientedCmp α cmp] {t : RBNode α} :
    (insert cmp t x).reverse = insert (flip cmp) t.reverse x := by
  simp [insert] <;> split <;> simp

theorem insert_setBlack {t : RBNode α} :
    (t.insert cmp v).setBlack = (t.ins cmp v).setBlack := by
  unfold insert; split <;> simp [setBlack_idem]

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

protected theorem RedRed.reverse : RedRed p t n → RedRed p t.reverse n
  | .balanced h => .balanced h.reverse
  | .redred hp ha hb => .redred hp hb.reverse ha.reverse

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
    (hl : l.Balanced c n) (hr : r.RedRed p n) : ∃ c, (balance2 l v r).Balanced c (n + 1) :=
  (hr.reverse.balance1 hl.reverse (v := v)).imp fun _ h => by simpa using h.reverse

/-- The `balance1` function does nothing if the first argument is already balanced. -/
theorem balance1_eq {l : RBNode α} {v : α} {r : RBNode α}
    (hl : l.Balanced c n) : balance1 l v r = node black l v r := by
  unfold balance1; split <;> first | rfl | nomatch hl

/-- The `balance2` function does nothing if the second argument is already balanced. -/
theorem balance2_eq {l : RBNode α} {v : α} {r : RBNode α}
    (hr : r.Balanced c n) : balance2 l v r = node black l v r :=
  (reverse_reverse _).symm.trans <| by simp [balance1_eq hr.reverse]

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
  | _, .balanced h => split <;> [exact ⟨_, h.setBlack⟩; exact ⟨_, _, h⟩]
  | _, .redred _ ha hb => have .node red .. := t; exact ⟨_, _, .black ha hb⟩

@[simp] theorem reverse_setRed {t : RBNode α} : (setRed t).reverse = setRed t.reverse := by
  unfold setRed; split <;> simp

protected theorem All.setRed {t : RBNode α} (h : t.All p) : (setRed t).All p := by
  unfold setRed; split <;> simp_all

/-- The `setRed` function preserves the ordering invariants. -/
protected theorem Ordered.setRed {t : RBNode α} : (setRed t).Ordered cmp ↔ t.Ordered cmp := by
  unfold setRed; split <;> simp [Ordered]

@[simp] theorem reverse_balLeft (l : RBNode α) (v : α) (r : RBNode α) :
    (balLeft l v r).reverse = balRight r.reverse v l.reverse := by
  unfold balLeft balRight; split
  · simp
  · rw [balLeft.match_2.eq_2 _ _ _ _ (by simp [reverse_eq_iff]; intros; solve_by_elim)]
    split <;> simp
    rw [balRight.match_1.eq_3] <;> (simp [reverse_eq_iff]; intros; solve_by_elim)

@[simp] theorem reverse_balRight (l : RBNode α) (v : α) (r : RBNode α) :
    (balRight l v r).reverse = balLeft r.reverse v l.reverse := by
  rw [← reverse_reverse (balLeft ..)]; simp

protected theorem All.balLeft
    (hl : l.All p) (hv : p v) (hr : r.All p) : (balLeft l v r).All p := by
  unfold balLeft; split <;> (try simp_all); split <;> simp_all [All.setRed]

/-- The `balLeft` function preserves the ordering invariants. -/
protected theorem Ordered.balLeft {l : RBNode α} {v : α} {r : RBNode α}
    (lv : l.All (cmpLT cmp · v)) (vr : r.All (cmpLT cmp v ·))
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
    (hl : l.All p) (hv : p v) (hr : r.All p) : (balRight l v r).All p :=
  All.reverse.1 <| reverse_balRight .. ▸ (All.reverse.2 hr).balLeft hv (All.reverse.2 hl)

/-- The `balRight` function preserves the ordering invariants. -/
protected theorem Ordered.balRight {l : RBNode α} {v : α} {r : RBNode α}
    (lv : l.All (cmpLT cmp · v)) (vr : r.All (cmpLT cmp v ·))
    (hl : l.Ordered cmp) (hr : r.Ordered cmp) : (balRight l v r).Ordered cmp := by
  rw [← reverse_reverse (balRight ..), reverse_balRight]
  exact .reverse <| hr.reverse.balLeft
    ((All.reverse.2 vr).imp cmpLT.flip) ((All.reverse.2 lv).imp cmpLT.flip) hl.reverse

/-- The balancing properties of the `balRight` function. -/
protected theorem Balanced.balRight (hl : l.Balanced cl (n + 1)) (hr : r.RedRed True n) :
    (balRight l v r).RedRed (cl = red) (n + 1) := by
  rw [← reverse_reverse (balRight ..), reverse_balRight]
  exact .reverse <| hl.reverse.balLeft hr.reverse

-- note: reverse_append is false!

protected theorem All.append (hl : l.All p) (hr : r.All p) : (append l r).All p := by
  unfold append; split <;> try simp [*]
  · have ⟨hx, ha, hb⟩ := hl; have ⟨hy, hc, hd⟩ := hr
    have := hb.append hc; split <;> simp_all
  · have ⟨hx, ha, hb⟩ := hl; have ⟨hy, hc, hd⟩ := hr
    have := hb.append hc; split <;> simp_all [All.balLeft]
  · simp_all [hl.append hr.2.1]
  · simp_all [hl.2.2.append hr]
termination_by l.size + r.size

/-- The `append` function preserves the ordering invariants. -/
protected theorem Ordered.append {l : RBNode α} {v : α} {r : RBNode α}
    (lv : l.All (cmpLT cmp · v)) (vr : r.All (cmpLT cmp v ·))
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
termination_by l.size + r.size

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
      exact .redred nofun (.red ha hb') (.red hc' hd)
    · next bcc _ H =>
      match bcc, append b c, IH, H with
      | black, _, IH, _ => exact .redred nofun ha (.red IH hd)
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
    exact .redred nofun IH hd
  · have .red ha hb := hl; have IH := hb.append hr
    have .black hc hd := hr; have ⟨c, IH⟩ := IH.of_false (· rfl rfl)
    exact .redred nofun ha IH
termination_by l.size + r.size

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
      | .node black .., _, ⟨n, rfl, ha⟩ => (hb.balLeft ha).of_false nofun
    · exact match b, n, ihb with
      | .nil, _, _ => ⟨_, .red ha hb⟩
      | .node black .., _, ⟨n, rfl, hb⟩ => (ha.balRight hb).of_false nofun
    · exact (ha.append hb).of_false (· rfl rfl)

/-- The `erase` function preserves the ordering invariants. -/
protected theorem Ordered.erase {t : RBNode α} (h : t.Ordered cmp) : (erase cut t).Ordered cmp :=
  Ordered.setBlack.2 h.del

/-- The `erase` function preserves the balance invariants. -/
protected theorem Balanced.erase {t : RBNode α}
    (h : t.Balanced c n) : ∃ n, (t.erase cut).Balanced black n :=
  have ⟨_, h⟩ := h.del.redred; h.setBlack

/-- The well-formedness invariant implies the ordering and balance properties. -/
theorem WF.out {t : RBNode α} (h : t.WF cmp) : t.Ordered cmp ∧ ∃ c n, t.Balanced c n := by
  induction h with
  | mk o h => exact ⟨o, _, _, h⟩
  | insert _ ih => have ⟨o, _, _, h⟩ := ih; exact ⟨o.insert, h.insert⟩
  | erase _ ih => have ⟨o, _, _, h⟩ := ih; exact ⟨o.erase, _, h.erase⟩

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
  lt_mono : cmpLT cmpα x y → cmpLT cmpβ (f x) (f y)

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
`O(n)`. Map a function on every value in the set.
This requires `IsMonotone` on the function in order to preserve the order invariant.
If the function is not monotone, use `RBSet.map` instead.
-/
@[inline] def mapMonotone (f : α → β) [IsMonotone cmpα cmpβ f] (t : RBSet α cmpα) : RBSet β cmpβ :=
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

open Ordering (byKey)

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
def mapVal (f : α → β → γ) (t : RBMap α β cmp) : RBMap α γ cmp := t.mapMonotone (Imp.mapSnd f)

end RBMap
