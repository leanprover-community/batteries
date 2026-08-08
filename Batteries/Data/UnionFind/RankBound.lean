/-
Copyright (c) 2024 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
module

import Batteries.Data.UnionFind.Lemmas

/-! # Rank-descendant bound for union-find

This file proves the fundamental rank invariant for union-find structures:
for every root node `i`, the number of descendants of `i` is at least `2^(rankD arr i)`.

The proof proceeds by induction on `UnionFind.WF`, the well-formedness witness.
-/

namespace Batteries.UnionFind

open UnionFind

/-! ## Counting utility -/

section Count

variable {p q : Nat → Prop} [DecidablePred p] [DecidablePred q]

/-- The number of naturals `j < n` satisfying `p`. -/
def countBelow (p : Nat → Prop) [DecidablePred p] (n : Nat) : Nat :=
  match n with
  | 0 => 0
  | n + 1 => countBelow p n + if p n then 1 else 0

@[simp] theorem countBelow_zero : countBelow p 0 = 0 := rfl

@[simp] theorem countBelow_succ :
    countBelow p (n + 1) = countBelow p n + if p n then 1 else 0 := rfl

theorem countBelow_le : countBelow p n ≤ n := by
  induction n with
  | zero => exact Nat.le_refl _
  | succ n ih => simp only [countBelow_succ]; split <;> omega

theorem countBelow_mono_pred (h : ∀ j, j < n → p j → q j) :
    countBelow p n ≤ countBelow q n := by
  induction n with
  | zero => exact Nat.le_refl _
  | succ n ih =>
    simp only [countBelow_succ]
    have := ih fun j hj => h j (Nat.lt_succ_of_lt hj)
    by_cases hp : p n <;> simp [hp]
    · have := h n (Nat.lt_succ_self _) hp; simp [this]; omega
    · omega

theorem countBelow_congr (h : ∀ j, j < n → (p j ↔ q j)) :
    countBelow p n = countBelow q n :=
  Nat.le_antisymm
    (countBelow_mono_pred fun j hj => (h j hj).mp)
    (countBelow_mono_pred fun j hj => (h j hj).mpr)

/-- Disjoint union: count(p ∨ q) = count(p) + count(q) when disjoint. -/
theorem countBelow_or_of_disjoint
    (hdisj : ∀ j, j < n → ¬(p j ∧ q j)) :
    countBelow (fun j => p j ∨ q j) n = countBelow p n + countBelow q n := by
  induction n with
  | zero => simp
  | succ n ih =>
    simp only [countBelow_succ]
    have ihm := ih fun j hj => hdisj j (Nat.lt_succ_of_lt hj)
    have hnn := hdisj n (Nat.lt_succ_self _)
    by_cases hp : p n <;> by_cases hq : q n
    · exact absurd ⟨hp, hq⟩ hnn
    · simp [hp, hq]; omega
    · simp [hp, hq]; omega
    · simp [hp, hq]; omega

end Count

/-! ## Subtree size -/

/-- The number of nodes whose root is `rootD self i`. -/
noncomputable def subtreeSize (self : UnionFind) (i : Nat) : Nat :=
  countBelow (fun j => self.rootD j = self.rootD i) self.size

/-! ## Proof irrelevance for rootD -/

/-- `rootD` depends only on the array, not on the proofs. -/
theorem rootD_proof_irrel {a : Array UFNode}
    {h₁ : ∀ {i}, i < a.size → parentD a i < a.size}
    {h₂ : ∀ {i}, parentD a i ≠ i → rankD a i < rankD a (parentD a i)}
    {h₃ : ∀ {i}, i < a.size → parentD a i < a.size}
    {h₄ : ∀ {i}, parentD a i ≠ i → rankD a i < rankD a (parentD a i)}
    (hw₁ hw₂ : WF a) :
    (UnionFind.mk a h₁ h₂ hw₁).rootD j = (UnionFind.mk a h₃ h₄ hw₂).rootD j :=
  rootD_ext fun _ => rfl

/-! ## Helper: rank increases along ancestor chains -/

theorem rankD_lt_of_isAncestor
    {arr : Array UFNode} {s t : Nat}
    (ih_rank : ∀ {i : Nat}, parentD arr i ≠ i → rankD arr i < rankD arr (parentD arr i))
    (hanc : IsAncestor arr s t) (hne : s ≠ t) :
    rankD arr s < rankD arr t := by
  induction hanc with
  | self => exact absurd rfl hne
  | @parent k tgt hpk _hanc' ih =>
    by_cases heq : parentD arr k = tgt
    · rw [← heq]; exact ih_rank hpk
    · exact Nat.lt_trans (ih_rank hpk) (ih heq)

/-! ## Helper: rootD stability under single-parent change -/

/-- If `self₂` differs from `self₁` only at node `z`'s parent,
`z` is a root in `self₁`, and `self₁.rootD j ≠ z`, then `self₂.rootD j = self₁.rootD j`.
(Since `z` is a root in `self₁`, no ancestor path passes through `z` except `z` itself.) -/
theorem rootD_of_parent_eq_except
    (self₁ self₂ : UnionFind)
    (z : Nat) (hz_root : self₁.parent z = z)
    (hpar : ∀ k, k ≠ z → self₂.parent k = self₁.parent k)
    (j : Nat) (hj : self₁.rootD j ≠ z) :
    self₂.rootD j = self₁.rootD j := by
  -- Key: self₁.rootD j ≠ z means j ≠ z (since z is a root, rootD z = z ≠ rootD j if j rooted elsewhere)
  -- More precisely: j's ancestor path in self₁ never reaches z.
  -- Proof: if j = z, then rootD(self₁, z) = z (since z is root). But hj says rootD j ≠ z. Contradiction.
  have hj_ne_z : j ≠ z := by
    intro heq; subst heq; exact hj (rootD_eq_self.mpr hz_root)
  if h : self₂.parent j = j then
    rw [rootD_eq_self.mpr h]
    -- j is root in self₂. Since j ≠ z, self₁.parent j = self₂.parent j = j
    have h₁ : self₁.parent j = j := (hpar j hj_ne_z).symm ▸ h
    rw [rootD_eq_self.mpr h₁]
  else
    have _ := Nat.sub_lt_sub_left (self₂.lt_rankMax j) (self₂.rank_lt h)
    rw [← rootD_parent self₂ j, hpar j hj_ne_z]
    have hrp : self₁.rootD (self₁.parent j) = self₁.rootD j := rootD_parent self₁ j
    have hne : self₁.rootD (self₁.parent j) ≠ z := hrp ▸ hj
    have ih := rootD_of_parent_eq_except self₁ self₂ z hz_root hpar (self₁.parent j) hne
    rw [ih, hrp]
termination_by self₂.rankMax - self₂.rank j
decreasing_by
  have hpj : self₂.parent j = self₁.parent j := hpar j hj_ne_z
  rw [← hpj]
  exact Nat.sub_lt_sub_left (self₂.lt_rankMax j) (self₂.rank_lt h)

/-! ## Helper: rootD follows ancestor chains -/

theorem rootD_of_isAncestor (self : UnionFind)
    {s t : Nat} (hanc : IsAncestor self.arr s t) :
    self.rootD s = self.rootD t := by
  induction hanc with
  | self => rfl
  | @parent k _ hpk _ ih => rw [← rootD_parent self k]; exact ih

/-! ## Helper: rootD preserved by path compression -/

/-- Path compression preserves rootD: if `self₂` differs from `self₁` only at node `z`
(whose parent changes to `r`), and `self₁.rootD z = r`, and `r` is a root in `self₁`,
then `self₂.rootD j = self₁.rootD j` for all `j`. -/
theorem rootD_compress_eq
    (self₁ self₂ : UnionFind)
    (z : Nat) (r : Nat)
    (hr_root : self₁.parent r = r)
    (hz_rootD : self₁.rootD z = r)
    (hpar : ∀ k, k ≠ z → self₂.parent k = self₁.parent k)
    (hpar_z : self₂.parent z = r)
    (j : Nat) : self₂.rootD j = self₁.rootD j := by
  if h : self₂.parent j = j then
    rw [rootD_eq_self.mpr h]
    by_cases hjz : j = z
    · subst hjz; rw [hpar_z] at h; rw [← h, rootD_eq_self.mpr hr_root]
    · have h₁ : self₁.parent j = j := by rw [← hpar j hjz]; exact h
      exact (rootD_eq_self.mpr h₁).symm
  else
    have _ := Nat.sub_lt_sub_left (self₂.lt_rankMax j) (self₂.rank_lt h)
    rw [← rootD_parent self₂ j]
    by_cases hjz : j = z
    · subst hjz; rw [hpar_z]
      have ih := rootD_compress_eq self₁ self₂ j r hr_root hz_rootD hpar hpar_z r
      rw [ih, rootD_eq_self.mpr hr_root, hz_rootD]
    · rw [hpar j hjz]
      have ih := rootD_compress_eq self₁ self₂ z r hr_root hz_rootD hpar hpar_z (self₁.parent j)
      rw [ih, rootD_parent]
termination_by self₂.rankMax - self₂.rank j
decreasing_by all_goals simp_all

/-! ## Auxiliary: the rank bound by induction on WF -/

/-- The combined inductive property: WF implies parentD_lt, rankD_lt,
and the rank-descendant bound. We prove all three simultaneously because
parentD_lt and rankD_lt are needed to construct the UnionFind for rootD,
and they can only be derived by induction on WF. -/
theorem wf_props (hw : WF a) :
    (∀ {i}, i < a.size → parentD a i < a.size) ∧
    (∀ {i}, parentD a i ≠ i → rankD a i < rankD a (parentD a i)) ∧
    (∀ hpar hrank, ∀ {i}, parentD a i = i → i < a.size →
      2 ^ rankD a i ≤
        countBelow (fun j => (UnionFind.mk a hpar hrank hw).rootD j = i) a.size) := by
  induction hw with
  | empty =>
    refine ⟨fun h => absurd h (Nat.not_lt_zero _),
            fun h => absurd (parentD_of_not_lt (Nat.not_lt_zero _)) h,
            fun _ _ {_} _ hi => absurd hi (Nat.not_lt_zero _)⟩
  | @push a₀ hw ih =>
    obtain ⟨ih_par, ih_rank, ih_bound⟩ := ih
    refine ⟨?_, ?_, ?_⟩
    -- parentD_lt for push
    · intro i hi
      rw [push_parentD, Array.size_push]
      rw [Array.size_push] at hi
      by_cases hlt : i < a₀.size
      · exact Nat.lt_succ_of_lt (ih_par hlt)
      · rw [parentD_of_not_lt (by omega)]; omega
    -- rankD_lt for push
    · intro i hi
      simp only [push_parentD, push_rankD] at hi ⊢
      exact ih_rank hi
    -- rank bound for push
    · intro hpar hrank i hroot hi
      simp only [push_parentD] at hroot
      simp only [push_rankD, Array.size_push]
      -- Construct the predecessor and successor UnionFind values
      let self₀ : UnionFind := ⟨a₀, ih_par, ih_rank, hw⟩
      let self₁ : UnionFind := ⟨_, hpar, hrank, .push hw⟩
      -- rootD on self₁ equals rootD on self₀
      have hroot_eq : ∀ x, self₁.rootD x = self₀.rootD x :=
        fun x => rootD_ext fun y => by
          change parentD (a₀.push ⟨a₀.size, 0⟩) y = parentD a₀ y
          exact push_parentD a₀
      by_cases hlt : i < a₀.size
      · -- Old root
        -- Relate goal's UnionFind to self₁ and self₀
        have hpi : ∀ j,
            (UnionFind.mk _ hpar hrank (.push hw)).rootD j = self₁.rootD j :=
          fun j => rootD_proof_irrel (.push hw) (.push hw)
        have ih_b := ih_bound ih_par ih_rank hroot hlt
        calc 2 ^ rankD a₀ i
            ≤ countBelow (fun j => self₀.rootD j = i) a₀.size := ih_b
          _ ≤ countBelow (fun j => self₁.rootD j = i) (a₀.size + 1) := by
              apply Nat.le_trans
              · exact countBelow_mono_pred fun j hj hpj => (hroot_eq j).symm ▸ hpj
              · simp only [countBelow_succ]; split <;> omega
          _ = countBelow (fun j => (UnionFind.mk _ hpar hrank (.push hw)).rootD j = i) (a₀.size + 1) := by
              exact countBelow_congr fun j _ => ⟨fun h => (hpi j) ▸ h, fun h => (hpi j).symm ▸ h⟩
      · -- New node: i = a₀.size, rank = 0
        have : i = a₀.size := by rw [Array.size_push] at hi; omega
        subst this
        simp only [rankD, show ¬a₀.size < a₀.size from Nat.lt_irrefl _, ↓reduceDIte, Nat.pow_zero]
        -- Relate the goal's UnionFind to self₁ using proof irrelevance
        have hpi : ∀ j,
            (UnionFind.mk _ hpar hrank (.push hw)).rootD j = self₁.rootD j :=
          fun j => rootD_proof_irrel (.push hw) (.push hw)
        simp only [countBelow_succ, hpi]
        have hself₁_root : self₁.rootD a₀.size = a₀.size := by
          rw [rootD_eq_self.mpr]
          change parentD (a₀.push ⟨a₀.size, 0⟩) a₀.size = a₀.size
          rw [push_parentD, parentD_of_not_lt (Nat.not_lt.mpr (Nat.le_refl _))]
        simp [hself₁_root]
  | @link a₀ hw x y hxroot hyroot ih =>
    obtain ⟨ih_par, ih_rank, ih_bound⟩ := ih
    -- Construct predecessor UnionFind and derive parentD_lt/rankD_lt for linkAux
    let self₀ : UnionFind := ⟨a₀, ih_par, ih_rank, hw⟩
    let link_uf := self₀.link x y hxroot hyroot
    -- link_uf.arr is linkAux self₀.arr x y which reduces via let-unfolding
    refine ⟨link_uf.parentD_lt, link_uf.rankD_lt, fun hpar hrank i hroot hi => ?_⟩
    simp only [linkAux_size] at hi
    let self₁ : UnionFind := ⟨linkAux a₀ x y, hpar, hrank, .link hw x y hxroot hyroot⟩
    have hpi : ∀ j, (UnionFind.mk (linkAux a₀ x y) hpar hrank
        (.link hw x y hxroot hyroot)).rootD j = self₁.rootD j :=
      fun j => rootD_proof_irrel (.link hw x y hxroot hyroot) (.link hw x y hxroot hyroot)
    simp only [linkAux_size, hpi]
    -- Helper: rootD for self₁ in terms of parentD on linkAux
    have hparent₁ : ∀ k, self₁.parent k = parentD (linkAux a₀ x y) k := fun _ => rfl
    -- Case analysis using by_cases instead of split for better control
    by_cases hxy : x.1 = (y : Nat)
    · -- Case x.1 = y: linkAux a₀ x y = a₀
      have hlaux : linkAux a₀ x y = a₀ := by simp [linkAux, hxy]
      have hroot₁ : ∀ j, self₁.rootD j = self₀.rootD j :=
        fun j => rootD_ext fun k => show parentD (linkAux a₀ x y) k = parentD a₀ k by rw [hlaux]
      have hrankD_eq : rankD (linkAux a₀ x y) i = rankD a₀ i := by rw [hlaux]
      rw [hrankD_eq]
      rw [parentD_linkAux, if_pos hxy] at hroot
      exact Nat.le_trans (ih_bound ih_par ih_rank hroot hi)
        (countBelow_mono_pred fun j _ hpj => by rw [hroot₁]; exact hpj)
    · -- Case x.1 ≠ y
      rw [parentD_linkAux] at hroot
      simp only [hxy, ↓reduceIte] at hroot
      by_cases hrlt : a₀[y.1].rank < a₀[x.1].rank
      · -- rank y < rank x: y's parent becomes x, y is no longer root
        simp only [hrlt, ↓reduceIte] at hroot
        by_cases hiy : (y : Nat) = i
        · -- y = i: hroot says x.1 = i, so x.1 = y, contradiction
          simp [hiy] at hroot; exact absurd (hroot.trans hiy.symm) hxy
        · -- y ≠ i: parentD a₀ i = i
          simp [hiy] at hroot
          -- rankD unchanged for i (linkAux only modifies y, and i ≠ y)
          have hrankD_eq : rankD (linkAux a₀ x y) i = rankD a₀ i := by
            unfold linkAux; simp only [hxy, ↓reduceIte, hrlt]
            show rankD (a₀.set ↑y ⟨↑x, a₀[↑y].rank⟩) i = rankD a₀ i
            unfold rankD; simp [Array.size_set, Array.getElem_set, hiy]
          rw [hrankD_eq]
          -- Every old descendant of i is still a descendant of i
          -- Key insight: y was a root so no path goes through y except y itself.
          -- Since i ≠ y, nodes with rootD = i don't have y on their path.
          -- Only y's parent changed, so rootD for these nodes is unchanged.
          -- Show: parent in self₁ agrees with self₀ except at y
          have hparent_eq : ∀ k, k ≠ (y : Nat) → self₁.parent k = self₀.parent k := by
            intro k hk
            show parentD (linkAux a₀ x y) k = parentD a₀ k
            rw [parentD_linkAux]; simp [hxy, hrlt, Ne.symm hk]
          -- Show: i is a root in self₁
          have hi_root₁ : self₁.parent i = i := by
            show parentD (linkAux a₀ x y) i = i
            rw [parentD_linkAux]; simp [hxy, hrlt, hiy, hroot]
          -- Use rootD_of_parent_eq_except: y is root in self₀, parent agrees except at y
          have hroot₁ : ∀ j, self₀.rootD j = i → self₁.rootD j = i := by
            intro j hj
            have hne : self₀.rootD j ≠ (y : Nat) := by rw [hj]; exact Ne.symm hiy
            rw [rootD_of_parent_eq_except self₀ self₁ y hyroot hparent_eq j hne, hj]
          exact Nat.le_trans (ih_bound ih_par ih_rank hroot hi)
            (countBelow_mono_pred fun j hj hpj => hroot₁ j hpj)
      · -- rank y ≥ rank x: x's parent becomes y
        simp only [hrlt, ↓reduceIte] at hroot
        by_cases hix : (x : Nat) = i
        · -- x = i: hroot says y = i, so x.1 = y, contradiction
          simp [hix] at hroot; exact absurd (hix.trans hroot.symm) hxy
        · -- x ≠ i: parentD a₀ i = i (i was a root in a₀)
          by_cases hreq : a₀[x.1].rank = a₀[y.1].rank
          · -- Equal ranks: x's parent = y, y's rank bumped
            simp [hix] at hroot
            by_cases hiy : i = (y : Nat)
            · -- MERGE CASE: i = y, equal ranks. y's rank becomes rank+1.
              -- subtree(y) = old subtree(x) ∪ old subtree(y), disjoint.
              -- |subtree(y)| ≥ 2^rank + 2^rank = 2^(rank+1).
              subst hiy
              -- rankD of y in linkAux = rankD a₀ y + 1
              have hrankD_y : rankD (linkAux a₀ x y) y = rankD a₀ y + 1 := by
                simp only [linkAux, hxy, ↓reduceIte, hreq, rankD]
                split <;> simp_all
              rw [hrankD_y]; simp only [Nat.pow_succ, Nat.mul_comm]
              -- All nodes in self₁ have rootD = x or rootD = y (by root_link)
              -- x and y have disjoint subtrees in self₀
              -- After link, all go to y (or to the chosen root)
              -- parents agree except at x
              have hparent_eq : ∀ k, k ≠ (x : Nat) → self₁.parent k = self₀.parent k := by
                intro k hk
                show parentD (linkAux a₀ x y) k = parentD a₀ k
                rw [parentD_linkAux]; simp [hxy, hrlt, Ne.symm hk]
              -- rootD(self₁, j) = y for any j whose old root was x or y
              -- rootD(self₁, j) = self₀.rootD j for j whose old root was neither
              -- Use root_link from Lemmas.lean to characterize rootD after link
              obtain ⟨r, hr_eq, hr_rootD⟩ := root_link (self := self₀) hxroot hyroot
              -- root_link gives: rootD(link, i) = if rootD(self₀, i) = x ∨ rootD(self₀, i) = y then r else rootD(self₀, i)
              -- r = x or r = y
              -- We need rootD(self₁, j) = rootD(link_uf, j) for all j, by proof irrelevance
              have hself₁_eq : ∀ j, self₁.rootD j = link_uf.rootD j := fun j => by
                exact rootD_ext (m1 := self₁) (m2 := link_uf) (fun _ => rfl)
              have hroot_x : ∀ j, self₀.rootD j = x → self₁.rootD j = y := by
                intro j hj
                rw [hself₁_eq]
                -- link_uf.rootD j = r (since rootD(self₀, j) = x ∈ {x, y})
                have h1 : link_uf.rootD j = r := by
                  rw [hr_rootD, if_pos (Or.inl hj)]
                -- r must be y: rootD(link, x) = r, but x's parent in link is y.
                -- So rootD(link, x) must reach y. Hence r = y (since r = rootD of merged tree).
                have hr_is_y : (r : Nat) = (y : Nat) := by
                  have h2 : link_uf.rootD (x : Nat) = r := by
                    rw [hr_rootD, if_pos (Or.inl (rootD_eq_self.mpr hxroot))]
                  -- link_uf.parent x = y (by linkAux with ¬hrlt)
                  have hpx : link_uf.parent (x : Nat) = (y : Nat) := by
                    show parentD link_uf.arr ↑x = ↑y
                    simp [show link_uf.arr = linkAux a₀ x y from rfl, parentD_linkAux, hxy, hrlt]
                  -- link_uf.parent y = y
                  have hpy : link_uf.parent (y : Nat) = (y : Nat) := by
                    show parentD link_uf.arr ↑y = ↑y
                    simp [show link_uf.arr = linkAux a₀ x y from rfl, parentD_linkAux, hxy, hrlt, hyroot]
                  -- rootD(link, x) = rootD(link, parent(x)) = rootD(link, y) = y
                  rw [← h2, ← rootD_parent link_uf (x : Nat), hpx,
                      rootD_eq_self.mpr hpy]
                rw [h1, hr_is_y]
              have hroot_y : ∀ j, self₀.rootD j = y → self₁.rootD j = y := by
                intro j hj
                have hne : self₀.rootD j ≠ (x : Nat) := by rw [hj]; exact Ne.symm hxy
                rw [rootD_of_parent_eq_except self₀ self₁ x hxroot hparent_eq j hne, hj]
              -- Count in self₁ with rootD = y ≥ count in self₀ with rootD = x + count with rootD = y
              have ih_x := ih_bound ih_par ih_rank hxroot (by exact x.2)
              have ih_y := ih_bound ih_par ih_rank hyroot (by exact y.2)
              have hrank_eq : rankD a₀ x = rankD a₀ y := by
                simp only [rankD, x.2, y.2, ↓reduceDIte]; exact hreq
              rw [hrank_eq] at ih_x
              calc 2 * 2 ^ rankD a₀ y
                  = 2 ^ rankD a₀ y + 2 ^ rankD a₀ y := by omega
                _ ≤ countBelow (fun j => self₀.rootD j = x) a₀.size +
                    countBelow (fun j => self₀.rootD j = y) a₀.size :=
                    Nat.add_le_add ih_x ih_y
                _ = countBelow (fun j => self₀.rootD j = x ∨ self₀.rootD j = y) a₀.size := by
                    rw [← countBelow_or_of_disjoint (fun j _ ⟨h1, h2⟩ => hxy (h1.symm.trans h2))]
                _ ≤ countBelow (fun j => self₁.rootD j = y) a₀.size :=
                    countBelow_mono_pred fun j _ h =>
                      h.elim (hroot_x j) (hroot_y j)
            · -- i ≠ x, i ≠ y: rankD unchanged, subtree preserved
              have hrankD_eq : rankD (linkAux a₀ x y) i = rankD a₀ i := by
                -- i ≠ x, i ≠ y, so rankD is unchanged through linkAux
                simp only [rankD, linkAux, hxy, ↓reduceIte, hreq]
                split <;> (first | rfl | simp_all [Ne.symm hiy])
              rw [hrankD_eq]
              have hparent_eq : ∀ k, k ≠ (x : Nat) → self₁.parent k = self₀.parent k := by
                intro k hk
                show parentD (linkAux a₀ x y) k = parentD a₀ k
                rw [parentD_linkAux]; simp [hxy, hrlt, Ne.symm hk]
              have hroot₁ : ∀ j, self₀.rootD j = i → self₁.rootD j = i := by
                intro j hj
                have hne : self₀.rootD j ≠ (x : Nat) := by rw [hj]; exact Ne.symm hix
                rw [rootD_of_parent_eq_except self₀ self₁ x hxroot hparent_eq j hne, hj]
              exact Nat.le_trans (ih_bound ih_par ih_rank hroot hi)
                (countBelow_mono_pred fun j hj hpj => hroot₁ j hpj)
          · -- Unequal ranks (rank x < rank y): x's parent = y, no rank bump
            simp [hix] at hroot
            have hrankD_eq : rankD (linkAux a₀ x y) i = rankD a₀ i := by
              unfold linkAux; simp only [hxy, ↓reduceIte, hrlt, hreq]
              show rankD (a₀.set ↑x ⟨↑y, a₀[↑x].rank⟩) i = rankD a₀ i
              simp [rankD, Array.size_set, Array.getElem_set, hix]
            rw [hrankD_eq]
            have hparent_eq : ∀ k, k ≠ (x : Nat) → self₁.parent k = self₀.parent k := by
              intro k hk
              show parentD (linkAux a₀ x y) k = parentD a₀ k
              rw [parentD_linkAux]; simp [hxy, hrlt, Ne.symm hk]
            have hroot₁ : ∀ j, self₀.rootD j = i → self₁.rootD j = i := by
              intro j hj
              have hne : self₀.rootD j ≠ (x : Nat) := by rw [hj]; exact Ne.symm hix
              rw [rootD_of_parent_eq_except self₀ self₁ x hxroot hparent_eq j hne, hj]
            exact Nat.le_trans (ih_bound ih_par ih_rank hroot hi)
              (countBelow_mono_pred fun j hj hpj => hroot₁ j hpj)
  | compress hw₀ cx cr hcr hcanc hcarr ih =>
    obtain ⟨ih_par, ih_rank, ih_bound⟩ := ih
    subst hcarr
    rename_i a₀
    -- parentD_lt for compress
    have compress_parentD_lt : ∀ {i},
        i < (a₀.modify ↑cx fun n => {parent := ↑cr, rank := n.rank}).size →
        parentD (a₀.modify ↑cx fun n => {parent := ↑cr, rank := n.rank}) i <
          (a₀.modify ↑cx fun n => {parent := ↑cr, rank := n.rank}).size := by
      intro i hi
      rw [Array.size_modify] at hi ⊢
      by_cases hix : i = (cx : Nat)
      · -- i = cx: parentD becomes cr
        subst hix
        simp only [parentD, Array.size_modify, cx.2, ↓reduceDIte, Array.getElem_modify, ↓reduceIte]
        exact cr.2
      · -- i ≠ cx: parentD unchanged
        simp only [parentD, Array.size_modify, Array.getElem_modify]
        split
        · rw [if_neg (Ne.symm hix)]; rw [← parentD_eq ‹_›]; exact ih_par ‹_›
        · exact absurd hi ‹_›
    -- rankD_lt for compress (rank is unchanged, parent may point to root instead)
    have compress_rankD_lt : ∀ {i},
        parentD (a₀.modify ↑cx fun n => {parent := ↑cr, rank := n.rank}) i ≠ i →
        rankD (a₀.modify ↑cx fun n => {parent := ↑cr, rank := n.rank}) i <
          rankD (a₀.modify ↑cx fun n => {parent := ↑cr, rank := n.rank})
            (parentD (a₀.modify ↑cx fun n => {parent := ↑cr, rank := n.rank}) i) := by
      intro i hne
      -- Helper: rankD unchanged by modify
      have hrankD_eq : ∀ k, rankD (a₀.modify ↑cx fun n => {parent := ↑cr, rank := n.rank}) k =
          rankD a₀ k := by
        intro k; simp only [rankD, Array.size_modify, Array.getElem_modify]
        split
        · split <;> simp
        · rfl
      -- Helper: parentD unchanged for k ≠ cx
      have hparentD_ne : ∀ k, k ≠ (cx : Nat) →
          parentD (a₀.modify ↑cx fun n => {parent := ↑cr, rank := n.rank}) k = parentD a₀ k := by
        intro k hk; simp only [parentD, Array.size_modify, Array.getElem_modify]
        split
        · rw [if_neg (Ne.symm hk)]
        · rfl
      -- Helper: parentD at cx = cr
      have hparentD_cx :
          parentD (a₀.modify ↑cx fun n => {parent := ↑cr, rank := n.rank}) cx = cr := by
        simp only [parentD, Array.size_modify, cx.2, ↓reduceDIte, Array.getElem_modify, ↓reduceIte]
      rw [hrankD_eq, hrankD_eq]
      by_cases hix : i = (cx : Nat)
      · subst hix; rw [hparentD_cx]
        exact rankD_lt_of_isAncestor ih_rank hcanc (by
          intro heq; rw [hparentD_cx, heq] at hne; exact hne rfl)
      · rw [hparentD_ne i hix]
        exact ih_rank (by rwa [← hparentD_ne i hix])
    -- rank bound for compress (rootD unchanged by path compression)
    have compress_bound : ∀ (hpar hrank) {i},
        parentD (a₀.modify ↑cx fun n => {parent := ↑cr, rank := n.rank}) i = i →
        i < (a₀.modify ↑cx fun n => {parent := ↑cr, rank := n.rank}).size →
        2 ^ rankD (a₀.modify ↑cx fun n => {parent := ↑cr, rank := n.rank}) i ≤
          countBelow (fun j => (UnionFind.mk _ hpar hrank
            (.compress hw₀ cx cr hcr hcanc rfl)).rootD j = i)
            (a₀.modify ↑cx fun n => {parent := ↑cr, rank := n.rank}).size := by
      intro hpar hrank i hroot hi
      rw [Array.size_modify] at hi ⊢
      -- Reuse helpers from compress_rankD_lt
      have hrankD_eq : ∀ k, rankD (a₀.modify ↑cx fun n => {parent := ↑cr, rank := n.rank}) k =
          rankD a₀ k := by
        intro k; simp only [rankD, Array.size_modify, Array.getElem_modify]
        split
        · split <;> simp
        · rfl
      rw [hrankD_eq]
      -- parentD a₀ i = i
      have hparentD_cx :
          parentD (a₀.modify ↑cx fun n => {parent := ↑cr, rank := n.rank}) cx = cr := by
        simp only [parentD, Array.size_modify, cx.2, ↓reduceDIte, Array.getElem_modify, ↓reduceIte]
      have hroot_a₀ : parentD a₀ i = i := by
        by_cases hix : i = (cx : Nat)
        · subst hix; rw [hparentD_cx] at hroot; rw [← hroot]; exact hcr
        · have : parentD (a₀.modify ↑cx fun n => {parent := ↑cr, rank := n.rank}) i =
              parentD a₀ i := by
            simp only [parentD, Array.size_modify, Array.getElem_modify]
            split
            · rw [if_neg (Ne.symm hix)]
            · exact absurd hi ‹_›
          rwa [this] at hroot
      -- rootD unchanged by compression
      let self_mod : UnionFind := ⟨_, hpar, hrank, .compress hw₀ cx cr hcr hcanc rfl⟩
      let self₀ : UnionFind := ⟨a₀, ih_par, ih_rank, hw₀⟩
      -- Parents agree except at cx
      have hpar_ne : ∀ k, k ≠ (cx : Nat) → self_mod.parent k = self₀.parent k := by
        intro k hk
        change parentD (a₀.modify ↑cx _) k = parentD a₀ k
        simp only [parentD, Array.size_modify, Array.getElem_modify]
        split
        · rw [if_neg (Ne.symm hk)]
        · rfl
      -- cx is a root in self₀ iff cx = cr. For rootD_of_parent_eq_except we need
      -- that cx is a root in self₀ — but it might not be!
      -- Alternative approach: prove rootD is unchanged by showing for all j,
      -- self_mod.rootD j = self₀.rootD j using the fact that compression
      -- only shortcuts paths without changing which root they reach.
      -- We use rootD_of_parent_eq_except with z = cx, which requires
      -- self₀.parent cx = cx. But cx might not be a root! However, it has cr as ancestor.
      -- Let's use a direct recursive proof instead.
      -- rootD(self₀, cx) = cr
      have hcx_root : self₀.rootD cx = cr := by
        suffices self₀.rootD cx = self₀.rootD cr by rw [this, rootD_eq_self.mpr hcr]
        exact rootD_of_isAncestor self₀ hcanc
      -- parentD(self_mod, cx) = cr
      have hpar_cx : self_mod.parent (cx : Nat) = (cr : Nat) := by
        change parentD (a₀.modify ↑cx _) ↑cx = ↑cr
        simp only [parentD, Array.size_modify, cx.2, ↓reduceDIte, Array.getElem_modify, ↓reduceIte]
      -- rootD is preserved by compression
      have rootD_unch : ∀ j, self_mod.rootD j = self₀.rootD j :=
        rootD_compress_eq self₀ self_mod cx cr hcr hcx_root
          hpar_ne hpar_cx
      calc 2 ^ rankD a₀ i
          ≤ countBelow (fun j => self₀.rootD j = i) a₀.size := ih_bound ih_par ih_rank hroot_a₀ hi
        _ = countBelow (fun j => self_mod.rootD j = i) a₀.size :=
            (countBelow_congr fun j _ =>
              ⟨fun h => rootD_unch j ▸ h, fun h => (rootD_unch j).symm ▸ h⟩).symm
        _ = countBelow (fun j => (UnionFind.mk _ hpar hrank _).rootD j = i) a₀.size :=
            countBelow_congr fun j _ =>
              ⟨fun h => (rootD_proof_irrel _ _).symm ▸ h, fun h => (rootD_proof_irrel _ _) ▸ h⟩
    exact ⟨compress_parentD_lt, compress_rankD_lt, compress_bound⟩

/-! ## Main theorem -/

/-- The rank-descendant bound for union-find: for every natural number `i` and
every union-find structure `uf`, exactly one of three things holds:
- `i` is out of bounds (`i ≥ uf.size`), or
- `i` is not a root (`uf.parent i ≠ i`), or
- the rank bound holds (`2 ^ uf.rank i ≤ uf.subtreeSize i`).

This is the fundamental invariant that makes union-find efficient:
every root with rank `r` has at least `2^r` descendants. -/
theorem rank_le_log_subtreeSize :
    ∀ (i : Nat) (uf : UnionFind),
    i ≥ uf.size ∨ 2 ^ uf.rank i ≤ uf.subtreeSize i := by
  intro i uf
  by_cases hi : i < uf.size
  · right
    -- subtreeSize counts nodes in rootD(i)'s equivalence class, so subtreeSize i = subtreeSize (rootD i)
    -- The root r = rootD i satisfies parent r = r, so wf_props gives 2^rank(r) ≤ subtreeSize(r)
    -- And rank i ≤ rank r (by le_rank_root), so 2^rank(i) ≤ 2^rank(r)
    have hroot_eq : uf.rootD i = uf.rootD (uf.rootD i) := rootD_rootD.symm
    -- subtreeSize i = subtreeSize (rootD i) because rootD(j) = rootD(i) ↔ rootD(j) = rootD(rootD(i))
    have hsubtree : uf.subtreeSize i = uf.subtreeSize (uf.rootD i) := by
      simp [subtreeSize, rootD_rootD]
    rw [hsubtree]
    -- rootD i is a root
    have hr_root : uf.parent (uf.rootD i) = uf.rootD i := parent_rootD uf i
    have hr_lt : uf.rootD i < uf.size := rootD_lt.mpr hi
    -- Apply the bound for the root
    obtain ⟨_, _, hbound⟩ := wf_props uf.valid
    have hi_root : uf.rootD (uf.rootD i) = uf.rootD i := rootD_rootD
    simp only [subtreeSize, hi_root]
    have h := hbound uf.parentD_lt uf.rankD_lt hr_root hr_lt
    have : (UnionFind.mk uf.arr uf.parentD_lt uf.rankD_lt uf.valid) = uf := by
      cases uf; rfl
    rw [this] at h
    -- 2^rank(i) ≤ 2^rank(rootD i) ≤ subtreeSize(rootD i)
    exact Nat.le_trans (Nat.pow_le_pow_right (by omega) le_rank_root) h
  · left; exact Nat.le_of_not_lt hi

end Batteries.UnionFind
