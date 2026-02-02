/-
Copyright (c) 2021 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Paulino, Floris van Doorn, Jannis Limperg
-/
module

@[expose] public section

/-!
## Definitions on Arrays

This file contains various definitions on `Array`. It does not contain
proofs about these definitions, those are contained in other files in `Batteries.Data.Array`.
-/

namespace Array

/--
Check whether `xs` and `ys` are equal as sets, i.e. they contain the same
elements when disregarding order and duplicates. `O(n*m)`! If your element type
has an `Ord` instance, it is asymptotically more efficient to sort the two
arrays, remove duplicates and then compare them elementwise.
-/
def equalSet [BEq α] (xs ys : Array α) : Bool :=
  xs.all (ys.contains ·) && ys.all (xs.contains ·)

set_option linter.unusedVariables.funArgs false in
/--
Returns the first minimal element among `d` and elements of the array.
If `start` and `stop` are given, only the subarray `xs[start:stop]` is
considered (in addition to `d`).
-/
@[inline]
protected def minWith [ord : Ord α]
    (xs : Array α) (d : α) (start := 0) (stop := xs.size) : α :=
  xs.foldl (init := d) (start := start) (stop := stop) fun min x =>
    if compare x min |>.isLT then x else min

set_option linter.unusedVariables.funArgs false in
/--
Find the first minimal element of an array. If the array is empty, `d` is
returned. If `start` and `stop` are given, only the subarray `xs[start:stop]` is
considered.
-/
@[inline]
protected def minD [ord : Ord α]
    (xs : Array α) (d : α) (start := 0) (stop := xs.size) : α :=
  if h: start < xs.size ∧ start < stop then
    xs.minWith xs[start] (start + 1) stop
  else
    d

set_option linter.unusedVariables.funArgs false in
/--
Find the first minimal element of an array. If the array is empty, `none` is
returned. If `start` and `stop` are given, only the subarray `xs[start:stop]` is
considered.
-/
@[inline]
protected def min? [ord : Ord α]
    (xs : Array α) (start := 0) (stop := xs.size) : Option α :=
  if h : start < xs.size ∧ start < stop then
    some $ xs.minD xs[start] start stop
  else
    none

set_option linter.unusedVariables.funArgs false in
/--
Find the first minimal element of an array. If the array is empty, `default` is
returned. If `start` and `stop` are given, only the subarray `xs[start:stop]` is
considered.
-/
@[inline]
protected def minI [ord : Ord α] [Inhabited α]
    (xs : Array α) (start := 0) (stop := xs.size) : α :=
  xs.minD default start stop

set_option linter.unusedVariables.funArgs false in
/--
Returns the first maximal element among `d` and elements of the array.
If `start` and `stop` are given, only the subarray `xs[start:stop]` is
considered (in addition to `d`).
-/
@[inline]
protected def maxWith [ord : Ord α]
    (xs : Array α) (d : α) (start := 0) (stop := xs.size) : α :=
  xs.minWith (ord := ord.opposite) d start stop

set_option linter.unusedVariables.funArgs false in
/--
Find the first maximal element of an array. If the array is empty, `d` is
returned. If `start` and `stop` are given, only the subarray `xs[start:stop]` is
considered.
-/
@[inline]
protected def maxD [ord : Ord α]
    (xs : Array α) (d : α) (start := 0) (stop := xs.size) : α :=
  xs.minD (ord := ord.opposite) d start stop

set_option linter.unusedVariables.funArgs false in
/--
Find the first maximal element of an array. If the array is empty, `none` is
returned. If `start` and `stop` are given, only the subarray `xs[start:stop]` is
considered.
-/
@[inline]
protected def max? [ord : Ord α]
    (xs : Array α) (start := 0) (stop := xs.size) : Option α :=
  xs.min? (ord := ord.opposite) start stop

set_option linter.unusedVariables.funArgs false in
/--
Find the first maximal element of an array. If the array is empty, `default` is
returned. If `start` and `stop` are given, only the subarray `xs[start:stop]` is
considered.
-/
@[inline]
protected def maxI [ord : Ord α] [Inhabited α]
    (xs : Array α) (start := 0) (stop := xs.size) : α :=
  xs.minI (ord := ord.opposite) start stop

/-!
### Safe Nat Indexed Array functions
The functions in this section offer variants of Array functions which use `Nat` indices
instead of `Fin` indices. All these functions have as parameter a proof that the index is
valid for the array. But this parameter has a default argument `by get_elem_tactic` which
should prove the index bound.
-/

/--
`setN a i h x` sets an element in a vector using a Nat index which is provably valid.
A proof by `get_elem_tactic` is provided as a default argument for `h`.
This will perform the update destructively provided that `a` has a reference count of 1 when called.
-/
abbrev setN (a : Array α) (i : Nat) (x : α) (h : i < a.size := by get_elem_tactic) : Array α :=
  a.set i x

/--
  This is guaranteed by the Array docs but it is unprovable.
  May be asserted to be true in an unsafe context via `Array.unsafe_size_fits_usize
-/
private abbrev SizeFitsUSize {a : Array α}: Prop := a.size < USize.size

@[grind .]
private theorem nat_index_eq_usize_index {n : Nat} {a : Array α}
    {h : a.SizeFitsUSize} {hn : n ≤ a.size} :
    (USize.ofNat n).toNat = n :=
  USize.toNat_ofNat_of_lt' (Nat.lt_of_le_of_lt ‹_› ‹_›)

/--
  This is guaranteed by the Array docs but it is unprovable.
  Can be used in unsafe functions to write more efficient implementations
  that avoid arbitrary precision integer arithmetic.
-/
private unsafe def unsafe_size_fits_usize {a : Array α} : SizeFitsUSize (a := a) :=
  lcProof

@[inline]
private def scanlMFast [Monad m] (f : β → α → m β) (init : β) (as : Array α)
    (start := 0) (stop := as.size) : m (Array β) :=
  let stop := min stop as.size
  let start := min start as.size
  loop f init as
    (start := USize.ofNat start) (stop := USize.ofNat stop)
    (h_stop := by grind only [USize.size_eq, USize.ofNat_eq_iff_mod_eq_toNat, = Nat.min_def])
    (acc := Array.mkEmpty <| stop - start + 1)
where
  @[specialize]
  loop (f : β → α → m β) (init: β) (as: Array α) (start stop : USize)
       (h_stop : stop.toNat ≤ as.size) (acc : Array β) : m (Array β) := do
    if h_lt: start < stop then
      let next ← f init (as.uget start <| Nat.lt_of_lt_of_le h_lt h_stop)
      loop f next as (start + 1) stop h_stop (acc.push init)
    else
      pure <| acc.push init
  termination_by stop.toNat - min start.toNat stop.toNat
  decreasing_by
      have : start < (start + 1) := by grind only [USize.size_eq]
      grind only [Nat.min_def, USize.lt_iff_toNat_lt]

/--
Fold an effectful function `f` over the array from the left, returning the list of partial results.
-/
@[implemented_by scanlMFast]
def scanlM [Monad m] (f : β → α → m β) (init : β) (as : Array α) (start := 0)
    (stop := as.size) : m (Array β) :=
  loop f init as (min start as.size) (min stop as.size) (Nat.min_le_right _ _) #[]
where
  /-- auxiliary tail-recursive function for scanlM -/
  loop (f : β → α → m β) (init : β ) (as : Array α) (start stop : Nat)
       (h_stop : stop ≤ as.size) (acc : Array β) : m (Array β) := do
    if h_lt : start < stop then
      loop f (← f init as[start]) as (start + 1) stop h_stop (acc.push init)
    else
      pure <| acc.push init

private theorem scanlM_loop_eq_scanlMFast_loop [Monad m]
    {f : β → α → m β} {init : β} {as : Array α} {h_size : as.SizeFitsUSize}
    {start stop : Nat} {h_start : start ≤ as.size}
    {h_stop : stop ≤ as.size} {acc : Array β} :
    scanlM.loop f init as start stop h_stop acc
      = scanlMFast.loop f init as (USize.ofNat start) (USize.ofNat stop)
      (by rw [USize.toNat_ofNat_of_lt' (Nat.lt_of_le_of_lt h_stop h_size)]; exact h_stop) acc := by
  generalize h_n : stop - start = n
  induction n using Nat.strongRecOn generalizing start acc init
  rename_i n ih
  rw [scanlM.loop, scanlMFast.loop]
  have h_stop_usize := nat_index_eq_usize_index (h := h_size) (hn := h_stop)
  have h_start_usize := nat_index_eq_usize_index (h := h_size) (hn := h_start)
  split
  case isTrue h_lt =>
    simp_all only [USize.toNat_ofNat', ↓reduceDIte, uget,
      show USize.ofNat start < USize.ofNat stop by simp_all [USize.lt_iff_toNat_lt]]
    apply bind_congr
    intro next
    have h_start_succ : USize.ofNat start + 1 = USize.ofNat (start + 1) := by
      simp_all only [← USize.toNat_inj, USize.toNat_add]
      grind only [USize.size_eq, nat_index_eq_usize_index]
    rw [h_start_succ]
    apply ih (stop - (start + 1)) <;> omega
  case isFalse h_nlt => grind [USize.lt_iff_toNat_lt]

-- this theorem establishes that given the (unprovable) assumption that as.size < USize.size,
-- the scanlMFast and scanlM are equivalent
private theorem scanlM_eq_scanlMFast [Monad m]
    {f : β → α → m β} {init : β} {as : Array α}
    {h_size : as.SizeFitsUSize} {start stop : Nat} :
    scanlM f init as start stop = scanlMFast f init as start stop := by
  unfold scanlM scanlMFast
  apply scanlM_loop_eq_scanlMFast_loop
  simp_all only [gt_iff_lt]
  apply Nat.min_le_right

@[inline]
private def scanrMFast [Monad m] (f : α → β → m β) (init : β) (as : Array α)
    (h_size : as.SizeFitsUSize) (start := as.size) (stop := 0) : m (Array β) :=
  let start := min start as.size
  let stop := min stop start
  loop f init as
    (start := USize.ofNat start) (stop := USize.ofNat stop)
    (h_start := by grind only [USize.size_eq, USize.ofNat_eq_iff_mod_eq_toNat, = Nat.min_def])
    (acc := Array.replicate (start - stop + 1) init)
    (by grind only [!Array.size_replicate, = Nat.min_def, Array.nat_index_eq_usize_index])
where
  @[specialize]
  loop (f : α → β → m β) (init : β) (as : Array α)
       (start stop : USize)
       (h_start : start.toNat ≤ as.size)
       (acc : Array β)
       (h_bound : start.toNat - stop.toNat  < acc.size) :
        m (Array β) := do
    if h_gt : stop < start then
      let startM1 := start - 1
      have : startM1 < start := by grind only [!USize.sub_add_cancel, USize.lt_iff_le_and_ne,
        USize.lt_add_one, USize.le_zero_iff]
      have : startM1.toNat < as.size := Nat.lt_of_lt_of_le ‹_› ‹_›
      have : (startM1 - stop) < (start - stop) := by grind only
        [!USize.sub_add_cancel, USize.sub_right_inj, USize.add_comm, USize.lt_add_one,
          USize.add_assoc, USize.add_right_inj]
      let next ← f (as.uget startM1 ‹_›) init
      loop f next as
        (start := startM1)
        (stop := stop)
        (h_start := Nat.le_of_succ_le_succ (Nat.le_succ_of_le ‹_›))
        (acc := acc.uset (startM1 - stop) next
          (by grind only [USize.toNat_sub_of_le, USize.le_of_lt, USize.lt_iff_toNat_lt]))
        (h_bound :=
          (by grind only [USize.toNat_sub_of_le, = uset_eq_set, = size_set, USize.size_eq]))
    else
      pure acc
  termination_by start.toNat - stop.toNat
  decreasing_by
    grind only [USize.lt_iff_toNat_lt, USize.toNat_sub,
      USize.toNat_sub_of_le, USize.le_iff_toNat_le]

@[inline]
private unsafe def scanrMUnsafe [Monad m] (f : α → β → m β) (init : β) (as : Array α)
    (start := as.size) (stop := 0) : m (Array β) :=
  scanrMFast (h_size := Array.unsafe_size_fits_usize) f init as (start := start) (stop := stop)

/--
Folds a monadic function over a list from the left, accumulating the partial results starting with
`init`. The accumulated value is combined with the each element of the list in order, using `f`.

The optional parameters `start` and `stop` control the region of the array to be folded. Folding
proceeds from `start` (inclusive) to `stop` (exclusive), so no folding occurs unless `start < stop`.
By default, the entire array is folded.

Examples:
```lean example
example [Monad m] (f : α → β → m α) :
    Array.scanlM (m := m) f x₀ #[a, b, c] = (do
      let x₁ ← f x₀ a
      let x₂ ← f x₁ b
      let x₃ ← f x₂ c
      pure #[x₀, x₁, x₂, x₃])
  := by rfl
```

```lean example
example [Monad m] (f : α → β → m α) :
    Array.scanlM (m := m) f x₀ #[a, b, c] (start := 1) = (do
      let x₁ ← f x₀ b
      let x₂ ← f x₁ c
      pure #[x₀, x₁, x₂])
  := by rfl
-/
@[implemented_by scanrMUnsafe]
def scanrM [Monad m]
    (f : α → β → m β) (init : β) (as : Array α) (start := as.size) (stop := 0) : m (Array β) :=
  let start := min start as.size
  loop f init as start stop (Nat.min_le_right _ _) #[]
where
  /-- auxiliary tail-recursive function for scanrM -/
  loop (f : α → β → m β) (init : β) (as : Array α)
       (start stop : Nat)
       (h_start : start ≤ as.size)
       (acc : Array β) :
       m (Array β) := do
    if h_gt : stop < start then
      let i := start - 1
      let next ← f as[i] init
      loop f next as i stop (by omega) (acc.push init)
    else
      pure <| acc.push init |>.reverse

/--
Fold a function `f` over the list from the left, returning the list of partial results.
```
scanl (· + ·) 0 #[1, 2, 3] = #[0, 1, 3, 6]
```
-/
@[inline]
def scanl (f : β → α → β) (init : β) (as : Array α) (start := 0) (stop := as.size) : Array β :=
  Id.run <| as.scanlM (pure <| f · ·) init start stop

/--
Fold a function `f` over the list from the right, returning the list of partial results.
```
scanl (+) 0 #[1, 2, 3] = #[0, 1, 3, 6]
```
-/
@[inline]
def scanr (f : α → β → β) (init : β) (as : Array α) (start := as.size) (stop := 0) : Array β :=
  Id.run <| as.scanrM (pure <| f · ·) init start stop

end Array

namespace Subarray

/--
Fold an effectful function `f` over the array from the left, returning the list of partial results.
-/
@[inline]
def scanlM [Monad m] (f : β → α → m β) (init : β) (as : Subarray α) : m (Array β) :=
  as.array.scanlM f init (start := as.start) (stop := as.stop)

/--
Fold an effectful function `f` over the array from the right, returning the list of partial results.
-/
@[inline]
def scanrM [Monad m] (f : α → β → m β) (init : β) (as : Subarray α) : m (Array β) :=
  as.array.scanrM f init (start := as.start) (stop := as.stop)

/--
Fold a pure function `f` over the array from the left, returning the list of partial results.
-/
@[inline]
def scanl (f : β → α → β) (init : β) (as : Subarray α): Array β :=
  as.array.scanl f init (start := as.start) (stop := as.stop)

/--
Fold a pure function `f` over the array from the left, returning the list of partial results.
-/
def scanr (f : α → β → β) (init : β) (as : Subarray α): Array β :=
  as.array.scanr f init (start := as.start) (stop := as.stop)

/--
Check whether a subarray is empty.
-/
@[inline]
def isEmpty (as : Subarray α) : Bool :=
  as.start == as.stop

/--
Check whether a subarray contains an element.
-/
@[inline]
def contains [BEq α] (as : Subarray α) (a : α) : Bool :=
  as.any (· == a)

/--
Remove the first element of a subarray. Returns the element and the remaining
subarray, or `none` if the subarray is empty.
-/
def popHead? (as : Subarray α) : Option (α × Subarray α) :=
  if h : as.start < as.stop
    then
      let head := as.array[as.start]'(Nat.lt_of_lt_of_le h as.stop_le_array_size)
      let tail :=
        ⟨{ as.internalRepresentation with
           start := as.start + 1
           start_le_stop := Nat.le_of_lt_succ $ Nat.succ_lt_succ h }⟩
      some (head, tail)
    else
      none

end Subarray
