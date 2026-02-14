/-
Copyright (c) 2024 Shreyas Srinivas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shreyas Srinivas, François G. Dorais, Chad Sharp
-/
module

@[expose] public section

/-!
# Vectors

`Vector α n` is a thin wrapper around `Array α` for arrays of fixed size `n`.
-/

namespace Vector

/--
Returns `true` when all elements of the vector are pairwise distinct using `==` for comparison.
-/
@[inline] def allDiff [BEq α] (as : Vector α n) : Bool :=
  as.toArray.allDiff

/--
Set an element of a vector using a `USize` index and a proof that the index is within bounds.
-/
@[inline]
def uset (xs : Vector α n) (i : USize) (v : α) (h : i.toNat < n) : Vector α n :=
  ⟨xs.toArray.uset i v (xs.size_toArray.symm ▸ h), by simp⟩

private theorem USize.succ_toNat {start stop : USize} {n : Nat}
    (h_lt : start < stop) (h_stop : stop.toNat ≤ n) (h_su : n < USize.size) :
    (start + 1).toNat = start.toNat + 1 := by
  have h_lt_nat := USize.lt_iff_toNat_lt.mp h_lt
  cases System.Platform.numBits_eq
  all_goals
    simp_all only [USize.size, USize.toNat_add, USize.reduceToNat]
    omega

private theorem USize.pred_toNat {i : USize}
    (h_gt : 0 < i) :
    (i - 1).toNat = i.toNat - 1 := by
  have h_gt_nat := USize.lt_iff_toNat_lt.mp h_gt
  have h_bound := i.toNat_lt_size
  cases System.Platform.numBits_eq
  all_goals
    simp_all only [USize.size, USize.toNat_sub, USize.reduceToNat]
    omega

private theorem USize.toNat_ofNat_eq  {i : Nat}
    (h : n < USize.size) (hn : i ≤ n) :
    (USize.ofNat i).toNat = i :=
  USize.toNat_ofNat_of_lt' (Nat.lt_of_le_of_lt ‹_› ‹_›)

@[inline]
private def scanlMFast [Monad m] (f : β → α → m β) (init : β) (as : Vector α n)
    (h_su : n < USize.size) : m (Vector β (n + 1)) :=
  loop init (i := 0) (n_usize := USize.ofNat n)
    (h_n := USize.toNat_ofNat_eq h_su (Nat.le_refl n))
    (h_i := by simp [USize.toNat_zero])
    (acc := Vector.emptyWithCapacity (n + 1))
where
  @[specialize]
  loop (cur : β) (i n_usize : USize) (h_n : n_usize.toNat = n)
      (h_i : i.toNat ≤ n) (acc : Vector β i.toNat) : m (Vector β (n + 1)) := do
    if h_lt : i < n_usize then
      have h_lt_nat : i.toNat < n := by rw [← h_n]; exact USize.lt_iff_toNat_lt.mp h_lt
      have h_inc : (i + 1).toNat = i.toNat + 1 := USize.succ_toNat h_lt (by omega) h_su
      let next ← f cur (as.uget i (by omega))
      loop next (i + 1) n_usize h_n (by omega) (acc.push cur |>.cast h_inc.symm)
    else
      have : i.toNat = n := by grind only [USize.lt_iff_toNat_lt]
      return acc.push cur |>.cast (by omega)
  termination_by n - i.toNat
  decreasing_by
    rw [h_inc]
    omega

@[inline]
private unsafe def scanlMUnsafe [Monad m] (f : β → α → m β) (init : β) (as : Vector α n) :
    m (Vector β (n + 1)) :=
  scanlMFast f init as lcProof

/--
Fold an effectful function `f` over the array from the left, returning the list of partial results.
-/
@[implemented_by scanlMUnsafe]
def scanlM [Monad m] (f : β → α → m β) (init : β) (as : Vector α n)
    : m (Vector β (n + 1)) :=
  loop init 0 (Nat.zero_le n) #v[]
where
  /-- Auxiliary tail-recursive function for scanlM -/
  loop (cur : β) (i : Nat) (hi : i ≤ n) (acc : Vector β i) :
      m (Vector β (n + 1)) := do
    if h_lt : i < n then
      let next ← f cur as[i]
      loop next (i + 1) (by omega) (acc.push cur)
    else
      return acc.push cur |>.cast (by omega)

@[inline]
private def scanrMFast [Monad m] (f : α → β → m β) (init : β) (as : Vector α n)
    (h_su : n < USize.size) : m (Vector β (n + 1)) :=
  have h_n := USize.toNat_ofNat_eq h_su (Nat.le_refl n)
  loop init (i := USize.ofNat n) (n_usize := USize.ofNat n)
    (h_n := h_n) (h_i := by simp [h_n]) (acc := Vector.replicate (n + 1) init)
where
  @[specialize]
  loop (cur : β) (i n_usize : USize) (h_n : n_usize.toNat = n)
      (h_i : i.toNat ≤ n) (acc : Vector β (n + 1)) : m (Vector β (n + 1)) := do
    if h_gt : 0 < i then
      have h_gt_nat : 0 < i.toNat := USize.lt_iff_toNat_lt.mp h_gt
      let pred := i - 1
      have h_pred : pred.toNat = i.toNat - 1 := USize.pred_toNat h_gt
      let next ← f (as.uget pred (by omega)) cur
      loop next pred n_usize h_n (by omega) (acc.uset pred cur (by omega))
    else
      return acc
  termination_by i.toNat
  decreasing_by
    rw [h_pred]
    omega

@[inline]
private unsafe def scanrMUnsafe [Monad m] (f : α → β → m β) (init : β) (as : Vector α n) :
    m (Vector β (n + 1)) :=
  scanrMFast f init as lcProof

/--
Fold an effectful function `f` over the array from the right, returning the list of partial results.
-/
@[implemented_by scanrMUnsafe]
def scanrM [Monad m] (f : α → β → m β) (init : β) (as : Vector α n) :
    m (Vector β (n + 1)) :=
  loop init n (Nat.le_refl n) (#v[].cast (by omega))
where
  /-- Auxiliary tail-recursive function for scanrM -/
  loop (cur : β) (i : Nat) (hi : i ≤ n) (acc : Vector β (n - i)) :
      m (Vector β (n + 1)) := do
    if h_gt : 0 < i then
      let next ← f as[i - 1] cur
      loop next (i - 1) (by omega) (acc.push cur |>.cast (by omega))
    else
      return (acc.push cur).reverse.cast (by omega)

/--
Fold a function `f` over the list from the left, returning the vector of partial results.
-/
@[inline]
def scanl (f : β → α → β) (init : β) (as : Vector α n) : Vector β (n + 1) :=
  Id.run <| as.scanlM (pure <| f · ·) init

/--
Fold a function `f` over the list from the right, returning the vector of partial results.
-/
@[inline]
def scanr (f : α → β → β) (init : β) (as : Vector α n) : Vector β (n + 1) :=
  Id.run <| as.scanrM (pure <| f · ·) init
