/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Mario Carneiro
-/
import Std.Order
import Std.Logic
import Std.Tactic.ShowTerm

/-!
# Red-black trees

This module implements a type `RBMap α β cmp` which is a functional data structure for
storing a key-value store in a binary search tree.

It is built on the simpler `RBTree α cmp` type, which stores a set of values of type `α`
using the function `cmp : α → α → Ordering` for determining the ordering relation.
The tree will never store two elements that compare `.eq` under the `cmp` function,
but the function does not have to satisfy `cmp x y = .eq → x = y`, and in the map case
`α` is a key-value pair and the `cmp` function only compares the keys.
-/

set_option linter.missingDocs false -- FIXME

namespace Std
namespace New -- TODO: lean4#1645

inductive RBColor where
  | red | black

inductive RBNode (α : Type u) where
  | nil
  | node (c : RBColor) (l : RBNode α) (v : α) (r : RBNode α)

namespace RBNode
variable {α : Type u} {β : α → Type v} {σ : Type w}
open RBColor

protected def min : RBNode α → Option α
  | nil            => none
  | node _ nil v _ => some v
  | node _ l _ _   => l.min

protected def max : RBNode α → Option α
  | nil            => none
  | node _ _ v nil => some v
  | node _ _ _ r   => r.max

@[specialize] def fold (v₀ : σ) (f : σ → α → σ → σ) : RBNode α → σ
  | nil          => v₀
  | node _ l v r => f (l.fold v₀ f) v (r.fold v₀ f)

@[specialize] def foldl (f : σ → α → σ) : (init : σ) → RBNode α → σ
  | b, nil          => b
  | b, node _ l v r => foldl f (f (foldl f b l) v) r

@[specialize] def forM [Monad m] (f : α → m Unit) : RBNode α → m Unit
  | nil          => pure ()
  | node _ l v r => do forM f l; f v; forM f r

@[specialize] def foldlM [Monad m] (f : σ → α → m σ) : (init : σ) → RBNode α → m σ
  | b, nil          => pure b
  | b, node _ l v r => do foldlM f (← f (← foldlM f b l) v) r

@[inline] protected def forIn [Monad m]
    (as : RBNode α) (init : σ) (f : α → σ → m (ForInStep σ)) : m σ := do
  let rec @[specialize] visit : RBNode α → σ → m (ForInStep σ)
    | nil,          b => return ForInStep.yield b
    | node _ l v r, b => do
      match ← visit l b with
      | r@(.done _) => return r
      | .yield b    =>
        match ← f v b with
        | r@(.done _) => return r
        | .yield b    => visit r b
  match ← visit as init with
  | .done b  => pure b
  | .yield b => pure b

@[specialize] def foldr (f : α → σ → σ) : RBNode α → (init : σ) → σ
  | nil,          b => b
  | node _ l v r, b => l.foldr f (f v (r.foldr f b))

@[specialize] def all (p : α → Bool) : RBNode α → Bool
  | nil          => true
  | node _ l v r => p v && all p l && all p r

@[specialize] def any (p : α → Bool) : RBNode α → Bool
  | nil          => false
  | node _ l v r => p v || any p l || any p r

@[simp] def All (p : α → Prop) : RBNode α → Prop
  | nil          => True
  | node _ l v r => p v ∧ All p l ∧ All p r

theorem All.imp (H : ∀ {x}, p x → q x) : ∀ {x : RBNode α}, x.All p → x.All q
  | nil => id
  | node .. => fun ⟨h, hl, hr⟩ => ⟨H h, hl.imp H, hr.imp H⟩

@[simp] def Any (p : α → Prop) : RBNode α → Prop
  | nil          => False
  | node _ l v r => p v ∨ Any p l ∨ Any p r

inductive Balanced : RBNode α → RBColor → Nat → Prop where
  | protected nil : Balanced nil black 0
  | protected red : Balanced x black n → Balanced y black n → Balanced (node red x v y) red n
  | protected black : Balanced x c₁ n → Balanced y c₂ n → Balanced (node black x v y) black (n + 1)

def cmpLt (cmp : α → α → Ordering) (x y : α) : Prop :=
  Nonempty (∀ [TransCmp cmp], cmp x y = .lt)

abbrev cmpGt (cmp : α → α → Ordering) (y x : α) : Prop := cmpLt cmp x y

theorem cmpLt.trans (h₁ : cmpLt cmp x y) (h₂ : cmpLt cmp y z) : cmpLt cmp x z :=
  ⟨TransCmp.lt_trans h₁.1 h₂.1⟩

theorem cmpLt.trans_l (H : cmpLt cmp x y) {a : RBNode α}
    (h : a.All (cmpLt cmp y)) : a.All (cmpLt cmp x) := h.imp fun h => H.trans h

theorem cmpLt.trans_r (H : cmpLt cmp x y) {a : RBNode α}
    (h : a.All (cmpGt cmp x)) : a.All (cmpGt cmp y) := h.imp fun h => h.trans H

variable (cmp : α → α → Ordering) in
def Ordered : RBNode α → Prop
  | nil => True
  | node _ a x b => a.All (cmpGt cmp x) ∧ b.All (cmpLt cmp x) ∧ a.Ordered ∧ b.Ordered

-- the first half of Okasaki's `balance`, concerning red-red sequences in the left child
@[inline] def balance1 : RBNode α → α → RBNode α → RBNode α
  | node red (node red a x b) y c, z, d
  | node red a x (node red b y c), z, d => node red (node black a x b) y (node black c z d)
  | a,                             x, b => node black a x b

theorem Ordered.balance1 {l : RBNode α} {v : α} {r : RBNode α}
    (lv : l.All (cmpGt cmp v)) (vr : r.All (cmpLt cmp v))
    (hl : l.Ordered cmp) (hr : r.Ordered cmp) : (balance1 l v r).Ordered cmp := by
  unfold balance1; split
  case _ a x b y c =>
    have ⟨yv, _, cv⟩ := lv; have ⟨xy, yc, hx, hc⟩ := hl
    exact ⟨xy, ⟨yv, yc, yv.trans_l vr⟩, hx, cv, vr, hc, hr⟩
  case _ a x b y c _ =>
    have ⟨_, _, yv, _, cv⟩ := lv; have ⟨ax, ⟨xy, xb, _⟩, ha, by_, yc, hb, hc⟩ := hl
    exact ⟨⟨xy, xy.trans_r ax, by_⟩, ⟨yv, yc, yv.trans_l vr⟩, ⟨ax, xb, ha, hb⟩, cv, vr, hc, hr⟩
  case _ => exact ⟨lv, vr, hl, hr⟩

@[simp] theorem balance1_All {l : RBNode α} {v : α} {r : RBNode α} :
    (balance1 l v r).All p ↔ p v ∧ l.All p ∧ r.All p := by
  unfold balance1; split <;> simp [and_assoc, and_left_comm]

-- the second half, concerning red-red sequences in the right child
@[inline] def balance2 : RBNode α → α → RBNode α → RBNode α
  | a, x, node red (node red b y c) z d
  | a, x, node red b y (node red c z d) => node red (node black a x b) y (node black c z d)
  | a, x, b                             => node black a x b

theorem Ordered.balance2 {l : RBNode α} {v : α} {r : RBNode α}
    (lv : l.All (cmpGt cmp v)) (vr : r.All (cmpLt cmp v))
    (hl : l.Ordered cmp) (hr : r.Ordered cmp) : (balance2 l v r).Ordered cmp := by
  unfold balance2; split
  case _ b y c z d =>
    have ⟨_, ⟨vy, vb, _⟩, _⟩ := vr; have ⟨⟨yz, _, cz⟩, zd, ⟨by_, yc, hy, hz⟩, hd⟩ := hr
    refine' ⟨⟨vy, vy.trans_r lv, by_⟩, ⟨yz, yc, yz.trans_l zd⟩, ⟨lv, vb, hl, hy⟩, cz, zd, hz, hd⟩
  case _ a x b y c _ =>
    have ⟨vx, va, _⟩ := vr; have ⟨ax, xy, ha, hy⟩ := hr
    exact ⟨⟨vx, vx.trans_r lv, ax⟩, xy, ⟨lv, va, hl, ha⟩, hy⟩
  case _ => exact ⟨lv, vr, hl, hr⟩

@[simp] theorem balance2_All {l : RBNode α} {v : α} {r : RBNode α} :
    (balance2 l v r).All p ↔ p v ∧ l.All p ∧ r.All p := by
  unfold balance2; split <;> simp [and_assoc, and_left_comm]

def isRed : RBNode α → Bool
  | node red .. => true
  | _           => false

protected theorem Balanced.isRed (h : Balanced t red n) : isRed t := by cases h <;> rfl
theorem Balanced.not_isRed (h : Balanced t black n) : ¬ isRed t := by cases h <;> intro.

def isBlack : RBNode α → Bool
  | node black .. => true
  | _             => false

def setBlack : RBNode α → RBNode α
  | nil          => nil
  | node _ l v r => node black l v r

protected theorem Ordered.setBlack {t : RBNode α} : (setBlack t).Ordered cmp ↔ t.Ordered cmp := by
  unfold setBlack; split <;> simp [Ordered]

protected theorem Balanced.setBlack : t.Balanced c n → ∃ n', (setBlack t).Balanced black n'
  | .nil => ⟨_, .nil⟩
  | .black hl hr | .red hl hr => ⟨_, hl.black hr⟩

section Insert

variable (cmp : α → α → Ordering) in
@[specialize] def ins (x : α) : RBNode α → RBNode α
  | nil => node red nil x nil
  | node red a y b =>
    match cmp x y with
    | Ordering.lt => node red (ins x a) y b
    | Ordering.gt => node red a y (ins x b)
    | Ordering.eq => node red a x b
  | node black a y b =>
    match cmp x y with
    | Ordering.lt => balance1 (ins x a) y b
    | Ordering.gt => balance2 a y (ins x b)
    | Ordering.eq => node black a x b

protected theorem All.ins {x : α} {t : RBNode α}
  (h₁ : p x) (h₂ : t.All p) : (ins cmp x t).All p := by
  induction t <;> unfold ins <;> simp [*] <;> split <;>
    cases ‹_=_› <;> split <;> simp at h₂ <;> simp [*]

protected theorem Ordered.ins : ∀ {t : RBNode α}, t.Ordered cmp → (ins cmp x t).Ordered cmp
  | nil, _ => ⟨⟨⟩, ⟨⟩, ⟨⟩, ⟨⟩⟩
  | node red a y b, ⟨ay, yb, ha, hb⟩ => by
    unfold ins; split
    case _ h => exact ⟨ay.ins ⟨h⟩, yb, ha.ins, hb⟩
    case _ h => exact ⟨ay, yb.ins ⟨LawfulCmp.cmp_eq_gt.1 h⟩, ha, hb.ins⟩
    case _ h => exact (⟨
      ay.imp fun ⟨h'⟩ => ⟨(TransCmp.cmp_congr_right h).trans h'⟩,
      yb.imp fun ⟨h'⟩ => ⟨(TransCmp.cmp_congr_left h).trans h'⟩, ha, hb⟩)
  | node black a y b, ⟨ay, yb, ha, hb⟩ => by
    unfold ins; split
    case _ h => exact ha.ins.balance1 (ay.ins ⟨h⟩) yb hb
    case _ h => exact ha.balance2 ay (yb.ins ⟨LawfulCmp.cmp_eq_gt.1 h⟩) hb.ins
    case _ h => exact (⟨
      ay.imp fun ⟨h'⟩ => ⟨(TransCmp.cmp_congr_right h).trans h'⟩,
      yb.imp fun ⟨h'⟩ => ⟨(TransCmp.cmp_congr_left h).trans h'⟩, ha, hb⟩)

@[specialize] def insert (cmp : α → α → Ordering) (t : RBNode α) (v : α) : RBNode α :=
  bif isRed t then (ins cmp v t).setBlack else ins cmp v t

protected theorem Ordered.insert (h : t.Ordered cmp) : (insert cmp t v).Ordered cmp := by
  unfold RBNode.insert cond; split <;> simp [Ordered.setBlack, h.ins (x := v)]

inductive InsBalanced : RBNode α → RBNode α → Nat → Prop where
  | balanced : Balanced t c n → InsBalanced t₀ t n
  | redL : Balanced a black n → Balanced b black n → Balanced c black n →
    InsBalanced (node red a₀ v₀ b₀) (node red (node red a x b) y c) n
  | redR : Balanced a black n → Balanced b black n → Balanced c black n →
    InsBalanced (node red a₀ v₀ b₀) (node red a x (node red b y c)) n

protected theorem Balanced.ins (cmp v) {t : RBNode α}
    (h : t.Balanced c n) : t.InsBalanced (ins cmp v t) n := by
  induction h with
  | nil => exact .balanced (.red .nil .nil)
  | @red a n b x hl hr ihl ihr =>
    simp [ins]; split
    · match ins cmp v a, ihl with
      | _, .balanced .nil => exact .balanced (.red .nil hr)
      | _, .balanced (.red ha hb) => exact .redL ha hb hr
      | _, .balanced (.black ha hb) => exact .balanced (.red (.black ha hb) hr)
    · match ins cmp v b, ihr with
      | _, .balanced .nil => exact .balanced (.red hl .nil)
      | _, .balanced (.red ha hb) => exact .redR hl ha hb
      | _, .balanced (.black ha hb) => exact .balanced (.red hl (.black ha hb))
    · exact .balanced (.red hl hr)
  | @black a ca n b cb x hl hr ihl ihr =>
    simp [ins]; split
    · unfold balance1; split
      case _ e _ => match ins cmp v a, ihl, e with
        | _, .redL ha hb hc, rfl => exact .balanced (.red (.black ha hb) (.black hc hr))
      case _ e _ => match ins cmp v a, ihl, e with
        | _, .redR ha hb hc, rfl => exact .balanced (.red (.black ha hb) (.black hc hr))
      case _ H1 H2 _ =>
        match ins cmp v a, ihl, H1, H2 with
        | _, .balanced hl, _, _ => exact .balanced (.black hl hr)
        | _, .redL .., H, _ | _, .redR .., _, H => cases H _ _ _ _ _ rfl
    · unfold balance2; split
      case _ e _ => match ins cmp v b, ihr, e with
        | _, .redL ha hb hc, rfl => exact .balanced (.red (.black hl ha) (.black hb hc))
      case _ e _ => match ins cmp v b, ihr, e with
        | _, .redR ha hb hc, rfl => exact .balanced (.red (.black hl ha) (.black hb hc))
      case _ H1 H2 =>
        match ins cmp v b, ihr, H1, H2 with
        | _, .balanced hr, _, _ => exact .balanced (.black hl hr)
        | _, .redL .., H, _ | _, .redR .., _, H => cases H _ _ _ _ _ rfl
    · exact .balanced (.black hl hr)

theorem Balanced.insert {t : RBNode α} (h : t.Balanced c n) :
    ∃ c' n', (insert cmp t v).Balanced c' n' := by
  unfold insert cond; match ins cmp v t, h.ins cmp v with
  | _, .balanced h => split; {exact ⟨_, h.setBlack⟩}; {exact ⟨_, _, h⟩}
  | _, .redL ha hb hc => simp [isRed, setBlack]; exact ⟨_, _, .black (.red ha hb) hc⟩
  | _, .redR ha hb hc => simp [isRed, setBlack]; exact ⟨_, _, .black ha (.red hb hc)⟩

end Insert

-- Okasaki's full `balance`
def balance (a : RBNode α) (v : α) (d : RBNode α) : RBNode α :=
  match a with
  | node red (node red a x b) y c
  | node red a x (node red b y c) => node red (node black a x b) y (node black c v d)
  | a => match d with
    | node red b y (node red c z d)
    | node red (node red b y c) z d => node red (node black a v b) y (node black c z d)
    | _                             => node black a v d

def setRed : RBNode α → RBNode α
  | node _ a v b => node red a v b
  | e            => e

def balLeft (l : RBNode α) (v : α) (r : RBNode α) : RBNode α :=
  match l with
  | node red a x b => node red (node black a x b) v r
  | l => match r with
    | node black a y b                => balance l v (node red a y b)
    | node red (node black a y b) z c => node red (node black l v a) y (balance b z (setRed c))
    | r                               => node red l v r -- unreachable

def balRight (l : RBNode α) (v : α) (r : RBNode α) : RBNode α :=
  match r with
  | node red b y c => node red l v (node black b y c)
  | r => match l with
    | node black a x b                => balance (node red a x b) v r
    | node red a x (node black b y c) => node red (balance (setRed a) x b) y (node black c v r)
    | l                               => node red l v r -- unreachable

@[simp] def size : RBNode α → Nat
  | nil => 0
  | node _ x _ y => x.size + y.size + 1

def appendTrees : RBNode α → RBNode α → RBNode α
  | nil, x => x
  | x, nil => x
  | node red a x b, node red c y d =>
    match appendTrees b c with
    | node red b' z c' => node red (node red a x b') z (node red c' y d)
    | bc               => node red a x (node red bc y d)
  | node black a x b, node black c y d =>
    match appendTrees b c with
    | node red b' z c' => node red (node black a x b') z (node black c' y d)
    | bc               => balLeft a x (node black bc y d)
  | a, node red b x c => node red (appendTrees a b) x c
  | node red a x b, c => node red a x (appendTrees b c)
termination_by _ x y => x.size + y.size

/-! ## erase -/

@[specialize] def del (cmp : α → Ordering) : RBNode α → RBNode α
  | nil           => nil
  | node _ a y b =>
    match cmp y with
    | .lt => if a.isBlack then balLeft (del cmp a) y b else node red (del cmp a) y b
    | .gt => if b.isBlack then balRight a y (del cmp b) else node red a y (del cmp b)
    | .eq => appendTrees a b

@[specialize] def erase (cmp : α → Ordering) (t : RBNode α) : RBNode α := (del cmp t).setBlack

section Membership

@[specialize] def find? (cmp : α → Ordering) : RBNode α → Option α
  | nil => none
  | node _ a y b =>
    match cmp y with
    | .lt => find? cmp a
    | .gt => find? cmp b
    | .eq => some y

/-- `lowerBound? cmp` retrieves the largest entry smaller than or equal to `cmp`, if it exists. -/
@[specialize] def lowerBound? (cmp : α → Ordering) : RBNode α → Option α → Option α
  | nil,          lb => lb
  | node _ a y b, lb =>
    match cmp y with
    | .lt => lowerBound? cmp a lb
    | .gt => lowerBound? cmp b (some y)
    | .eq => some y

end Membership

@[specialize] def map {α : Type u} (f : α → α) : RBNode α → RBNode α
  | nil => nil
  | node c l v r => node c (l.map f) (f v) (r.map f)

def toArray (n : RBNode α) : Array α := n.foldl (init := #[]) (·.push)

instance : EmptyCollection (RBNode α) := ⟨nil⟩

end RBNode

open RBNode

def RBTree (α : Type u) (cmp : α → α → Ordering) : Type u :=
  {t : RBNode α // t.Ordered cmp ∧ ∃ c n, t.Balanced c n}

@[inline] def mkRBTree (α : Type u) (cmp : α → α → Ordering) : RBTree α cmp :=
  ⟨.nil, ⟨⟩, _, _, .nil⟩

namespace RBTree

@[inline] def empty : RBTree α cmp := mkRBTree ..

instance (α : Type u) (cmp : α → α → Ordering) : EmptyCollection (RBTree α cmp) :=
  ⟨empty⟩

instance (α : Type u) (cmp : α → α → Ordering) : Inhabited (RBTree α cmp) := ⟨∅⟩

@[inline] def foldl (f : σ → α → σ) : (init : σ) → RBTree α cmp → σ
  | b, ⟨t, _⟩ => t.foldl f b

@[inline] def foldr (f : α → σ → σ) : (init : σ) → RBTree α cmp → σ
  | b, ⟨t, _⟩ => t.foldr f b

@[inline] def foldlM [Monad m] (f : σ → α → m σ) : (init : σ) → RBTree α cmp → m σ
  | b, ⟨t, _⟩ => t.foldlM f b

@[inline] def forM [Monad m] (f : α → m PUnit) (t : RBTree α cmp) : m PUnit :=
  t.foldlM (fun _ v => f v) ⟨⟩

instance : ForIn m (RBTree α cmp) α where
  forIn t init f := t.val.forIn init f

@[inline] def isEmpty : RBTree α cmp → Bool
  | ⟨nil, _⟩ => true
  | _        => false

@[specialize] def toList (t : RBTree α cmp) : List α := t.1.foldr (·::·) []

/-- Returns the entry `a` such that `a ≤ k` for all keys in the RBTree. -/
@[inline] protected def min (t : RBTree α cmp) : Option α := t.1.min

/-- Returns the entry `a` such that `a ≥ k` for all keys in the RBTree. -/
@[inline] protected def max (t : RBTree α cmp) : Option α := t.1.max

instance [Repr α] : Repr (RBTree α cmp) where
  reprPrec m prec := Repr.addAppParen ("Std.rbmapOf " ++ repr m.toList) prec

@[inline] def insert (t : RBTree α cmp) (v : α) : RBTree α cmp :=
  ⟨t.1.insert cmp v, let ⟨o, _, _, h⟩ := t.2; ⟨o.insert, h.insert⟩⟩

-- TODO
-- @[inline] def erase : RBTree α cmp → α → RBTree α cmp
--   | ⟨t, w⟩, k => ⟨t.erase cmp k, WellFormed.eraseWff w rfl⟩

@[inline] def findP? (t : RBTree α cmp) (cut : α → Ordering) : Option α := t.1.find? cut

@[inline] def find? (t : RBTree α cmp) (x : α) : Option α := t.1.find? (cmp x)

@[inline] def findPD (t : RBTree α cmp) (cut : α → Ordering) (v₀ : α) : α := (t.findP? cut).getD v₀

/--
`lowerBoundP cut` retrieves the largest entry comparing `lt` or `eq` under `cut`, if it exists.
-/
@[inline] def lowerBoundP? (t : RBTree α cmp) (cut : α → Ordering) : Option α :=
  t.1.lowerBound? cut none

/-- `lowerBound? k` retrieves the largest entry smaller than or equal to `k`, if it exists. -/
@[inline] def lowerBound? (t : RBTree α cmp) (k : α) : Option α := t.1.lowerBound? (cmp k) none

/-- Returns true if the given cut returns `eq` for something in the RBTree. -/
@[inline] def containsP (t : RBTree α cmp) (cut : α → Ordering) : Bool := (t.findP? cut).isSome

/-- Returns true if the given key `a` is in the RBTree. -/
@[inline] def contains (t : RBTree α cmp) (a : α) : Bool := (t.find? a).isSome

@[inline] def ofList (l : List α) (cmp : α → α → Ordering) : RBTree α cmp :=
  l.foldl (fun r p => r.insert p) (mkRBTree α cmp)

@[inline] def ofArray (l : Array α) (cmp : α → α → Ordering) : RBTree α cmp :=
  l.foldl (fun r p => r.insert p) (mkRBTree α cmp)

/-- Returns true if the given predicate is true for all items in the RBTree. -/
@[inline] def all (t : RBTree α cmp) (p : α → Bool) : Bool := t.1.all p

/-- Returns true if the given predicate is true for any item in the RBTree. -/
@[inline] def any (t : RBTree α cmp) (p : α → Bool) : Bool := t.1.any p

/-- The number of items in the RBTree. -/
def size (m : RBTree α cmp) : Nat := m.1.size

@[inline] def min! [Inhabited α] (t : RBTree α cmp) : α := t.min.getD (panic! "map is empty")

@[inline] def max! [Inhabited α] (t : RBTree α cmp) : α := t.max.getD (panic! "map is empty")

/-- Attempts to find the value with key `k : α` in `t` and panics if there is no such key. -/
@[inline] def findP! [Inhabited α] (t : RBTree α cmp) (cut : α → Ordering) : α :=
  (t.findP? cut).getD (panic! "key is not in the map")

/-- Attempts to find the value with key `k : α` in `t` and panics if there is no such key. -/
@[inline] def find! [Inhabited α] (t : RBTree α cmp) (k : α) : α :=
  (t.find? k).getD (panic! "key is not in the map")

/--
Merges the maps `t₁` and `t₂`. If equal keys exist in both,
then use `mergeFn a₁ a₂` to produce the new merged value.
-/
def mergeBy (mergeFn : α → α → α) (t₁ t₂ : RBTree α cmp) : RBTree α cmp :=
  t₂.foldl (init := t₁) fun t₁ a₂ =>
    t₁.insert <| match t₁.find? a₂ with | some a₁ => mergeFn a₁ a₂ | none => a₂

/-- Intersects the maps `t₁` and `t₂` using `mergeFn a b` to produce the new value. -/
def intersectBy (cmp : α → β → Ordering) (mergeFn : α → β → γ)
    (t₁ : RBTree α cmpα) (t₂ : RBTree β cmpβ) : RBTree γ cmpγ :=
  t₁.foldl (init := ∅) fun acc a =>
      match t₂.findP? (cmp a) with
      | some b => acc.insert <| mergeFn a b
      | none => acc

end RBTree

/- TODO(Leo): define dRBMap -/

def RBMap (α : Type u) (β : Type v) (cmp : α → α → Ordering) : Type (max u v) :=
  RBTree (α × β) (fun a b => cmp a.1 b.1)

@[inline] def mkRBMap (α : Type u) (β : Type v) (cmp : α → α → Ordering) : RBMap α β cmp :=
  mkRBTree ..

@[inline] def RBMap.empty {α : Type u} {β : Type v} {cmp : α → α → Ordering} : RBMap α β cmp :=
  mkRBMap ..

instance (α : Type u) (β : Type v) (cmp : α → α → Ordering) : EmptyCollection (RBMap α β cmp) :=
  ⟨RBMap.empty⟩

instance (α : Type u) (β : Type v) (cmp : α → α → Ordering) : Inhabited (RBMap α β cmp) := ⟨∅⟩

namespace RBMap
variable {α : Type u} {β : Type v} {σ : Type w} {cmp : α → α → Ordering}

@[inline] def foldl (f : σ → α → β → σ) : (init : σ) → RBMap α β cmp → σ
  | b, ⟨t, _⟩ => t.foldl (fun s (a, b) => f s a b) b

@[inline] def foldr (f : α → β → σ → σ) : (init : σ) → RBMap α β cmp → σ
  | b, ⟨t, _⟩ => t.foldr (fun (a, b) s => f a b s) b

@[inline] def foldlM [Monad m] (f : σ → α → β → m σ) : (init : σ) → RBMap α β cmp → m σ
  | b, ⟨t, _⟩ => t.foldlM (fun s (a, b) => f s a b) b

@[inline] def forM [Monad m] (f : α → β → m PUnit) (t : RBMap α β cmp) : m PUnit :=
  t.foldlM (fun _ k v => f k v) ⟨⟩

instance : ForIn m (RBMap α β cmp) (α × β) where
  forIn t init f := t.val.forIn init f

@[inline] def isEmpty : RBMap α β cmp → Bool := RBTree.isEmpty

@[inline] def toList : RBMap α β cmp → List (α × β) := RBTree.toList

/-- Returns the kv pair `(a,b)` such that `a ≤ k` for all keys in the RBMap. -/
@[inline] protected def min : RBMap α β cmp → Option (α × β) := RBTree.min

/-- Returns the kv pair `(a,b)` such that `a ≥ k` for all keys in the RBMap. -/
@[inline] protected def max : RBMap α β cmp → Option (α × β) := RBTree.max

instance [Repr α] [Repr β] : Repr (RBMap α β cmp) where
  reprPrec m prec := Repr.addAppParen ("RBMap.fromList " ++ repr m.toList) prec

@[inline] def insert (t : RBMap α β cmp) (k : α) (v : β) : RBMap α β cmp := RBTree.insert t (k, v)

-- TODO
-- @[inline] def erase : RBMap α β cmp → α → RBMap α β cmp
--   | ⟨t, w⟩, k => ⟨t.erase cmp k, WellFormed.eraseWff w rfl⟩

@[inline] def ofList (l : List (α × β)) (cmp : α → α → Ordering) : RBMap α β cmp :=
  RBTree.ofList l _

@[inline] def ofArray (l : Array (α × β)) (cmp : α → α → Ordering) : RBMap α β cmp :=
  RBTree.ofArray l _

@[inline] def findEntry? (t : RBMap α β cmp) (k : α) : Option (α × β) := t.findP? (cmp k ·.1)

@[inline] def find? (t : RBMap α β cmp) (k : α) : Option β := t.findEntry? k |>.map (·.2)

@[inline] def findD (t : RBMap α β cmp) (k : α) (v₀ : β) : β := (t.find? k).getD v₀

/-- (lowerBound k) retrieves the kv pair of the largest key smaller than or equal to `k`,
    if it exists. -/
@[inline] def lowerBound (t : RBMap α β cmp) (k : α) : Option (α × β) :=
   RBTree.lowerBoundP? t (cmp k ·.1)

/-- Returns true if the given key `a` is in the RBMap.-/
@[inline] def contains (t : RBMap α β cmp) (a : α) : Bool := (t.findEntry? a).isSome

/-- Returns true if the given predicate is true for all items in the RBMap. -/
@[inline] def all (t : RBMap α β cmp) (p : α → β → Bool) : Bool := RBTree.all t fun (a, b) => p a b

/-- Returns true if the given predicate is true for any item in the RBMap. -/
@[inline] def any (t : RBMap α β cmp) (p : α → β → Bool) : Bool := RBTree.all t fun (a, b) => p a b

/-- The number of items in the RBMap. -/
def size : RBMap α β cmp → Nat := RBTree.size

@[inline] def min! [Inhabited α] [Inhabited β] : RBMap α β cmp → α × β := RBTree.min!

@[inline] def max! [Inhabited α] [Inhabited β] : RBMap α β cmp → α × β := RBTree.max!

/-- Attempts to find the value with key `k : α` in `t` and panics if there is no such key. -/
@[inline] def find! [Inhabited β] (t : RBMap α β cmp) (k : α) : β :=
  (t.find? k).getD (panic! "key is not in the map")

/-- Merges the maps `t₁` and `t₂`, if a key `a : α` exists in both,
then use `mergeFn a b₁ b₂` to produce the new merged value. -/
def mergeBy (mergeFn : α → β → β → β) (t₁ t₂ : RBMap α β cmp) : RBMap α β cmp :=
  RBTree.mergeBy (fun (_, b₁) (a, b₂) => (a, mergeFn a b₁ b₂)) t₁ t₂

/-- Intersects the maps `t₁` and `t₂` using `mergeFn a b₁ b₂` to produce the new value. -/
def intersectBy (mergeFn : α → β → γ → δ)
    (t₁ : RBMap α β cmp) (t₂ : RBMap α γ cmp) : RBMap α δ cmp :=
  RBTree.intersectBy (cmp ·.1 ·.1) (fun (a, b₁) (_, b₂) => (a, mergeFn a b₁ b₂)) t₁ t₂

end RBMap
end Std.New
open Std.New

def List.toRBMap (l : List (α × β)) (cmp : α → α → Ordering) : RBMap α β cmp := RBMap.ofList l cmp
