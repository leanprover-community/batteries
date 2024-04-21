/-
Copyright (c) 2024 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Mario Carneiro
-/
import Std.Data.Array.Perm

namespace Array

section «deleteme lean4#3933»
#guard_msgs(drop warning) in #check_failure Array.qpartition.maybeSwap

/-- Partitions `as[lo..=hi]`, returning a pivot point and the new array. -/
@[inline] def qpartition' (as : {as : Array α // as.size = n})
    (lt : α → α → Bool) (lo hi : Fin n) (hle : lo ≤ hi) :
    {as : Array α // as.size = n} × {pivot : Fin n // lo ≤ pivot ∧ pivot ≤ hi} :=
  let mid : Fin n := ⟨(lo.1 + hi) / 2, by omega⟩
  let rec
  /-- Swaps `lo` and `hi` if needed to ensure `as[lo] ≤ as[hi]`. -/
  @[inline] maybeSwap
      (as : {as : Array α // as.size = n}) (lo hi : Fin n) : {as : Array α // as.size = n} :=
    let hi := hi.cast as.2.symm
    let lo := lo.cast as.2.symm
    if lt (as.1.get hi) (as.1.get lo) then
      ⟨as.1.swap lo hi, (Array.size_swap ..).trans as.2⟩
    else as
  let as := maybeSwap as lo mid
  let as := maybeSwap as lo hi
  let as := maybeSwap as hi mid
  let_fun pivot := as.1.get (hi.cast as.2.symm)
  let rec
  /-- Inner loop of `qpartition`, where `as[lo..i]` are less than the pivot and `as[i..j]` are
  more than the pivot. -/
  loop (as : {as : Array α // as.size = n}) (i j : Fin n) (H : lo ≤ i ∧ i ≤ j ∧ j ≤ hi) :
      {as : Array α // as.size = n} × {pivot : Fin n // lo ≤ pivot ∧ pivot ≤ hi} :=
    have ⟨loi, ij, jhi⟩ := H
    if h : j < hi then by
      -- FIXME: if we don't clear these variables, `omega` will revert/intro them
      -- and as a result `loop` will spuriously depend on the extra `as` variables,
      -- breaking linearity
      rename_i as₁ as₂ as₃ as₄; clear as₁ mid as₂ as₃ as₄
      exact if lt (as.1.get (j.cast as.2.symm)) pivot then
        let as := ⟨as.1.swap (i.cast as.2.symm) (j.cast as.2.symm), (Array.size_swap ..).trans as.2⟩
        loop as ⟨i.1+1, by omega⟩ ⟨j.1+1, by omega⟩
          ⟨Nat.le_succ_of_le H.1, Nat.succ_le_succ ij, Nat.succ_le_of_lt h⟩
      else
        loop as i ⟨j.1+1, by omega⟩ ⟨loi, Nat.le_succ_of_le ij, Nat.succ_le_of_lt h⟩
    else
      let as := ⟨as.1.swap (i.cast as.2.symm) (hi.cast as.2.symm), (Array.size_swap ..).trans as.2⟩
      ⟨as, i, loi, Nat.le_trans ij jhi⟩
  termination_by hi.1 - j
  loop as lo lo ⟨Nat.le_refl _, Nat.le_refl _, hle⟩

/-- Sort the array `as[low..=high]` using comparator `lt`. -/
@[inline] def qsort' (as : Array α) (lt : α → α → Bool) (low := 0) (high := as.size - 1) :
    Array α :=
  let rec
  /-- Inner loop of `qsort`, which sorts `as[lo..=hi]`. -/
  @[specialize] sort {n} (as : {as : Array α // as.size = n})
      (lo : Nat) (hi : Fin n) : {as : Array α // as.size = n} :=
    if h : lo < hi.1 then
      let ⟨as, mid, (_ : lo ≤ mid), _⟩ :=
        qpartition' as lt ⟨lo, Nat.lt_trans h hi.2⟩ hi (Nat.le_of_lt h)
      let as := sort as lo ⟨mid - 1, by omega⟩
      sort as (mid + 1) hi
    else as
  termination_by hi - lo
  if low < high then
    if h : high < as.size then
      (sort ⟨as, rfl⟩ low ⟨high, h⟩).1
    else
      have := Inhabited.mk as
      panic! "index out of bounds"
  else as

end «deleteme lean4#3933»

open List

namespace QSort

/--
An array with externally counted length `n`.

TODO: This type is an implementation detail of `Array.qsort`, which may be replaced by a real
API later.
-/
def Vector (α n) := {as : Array α // as.size = n}

/-- Get the `i`th element of the array `as`. -/
def Vector.get (as : Vector α n) (i : Fin n) := as.1.get (i.cast as.2.symm)

/-- Swap elements `i` and `j` in array `as`. -/
def Vector.swap (as : Vector α n) (i j : Fin n) : Vector α n :=
  ⟨as.1.swap (i.cast as.2.symm) (j.cast as.2.symm), (size_swap ..).trans as.2⟩

/-- `PermStabilizing lo hi as as'` asserts that `as` and `as'` are permutations of each other,
and moreover they agree outside the range `lo..hi`. -/
def PermStabilizing (lo hi : Nat) (as as' : Vector α n) :=
  as.1.data ~ as'.1.data ∧ ∀ i : Fin n, ¬(lo ≤ i ∧ i < hi) → as.get i = as'.get i

@[refl] protected theorem PermStabilizing.rfl :
    PermStabilizing lo hi as as := ⟨.refl _, fun _ _ => .refl _⟩

protected theorem PermStabilizing.trans
    (h1 : PermStabilizing lo hi as₁ as₂) (h2 : PermStabilizing lo hi as₂ as₃) :
    PermStabilizing lo hi as₁ as₃ :=
  ⟨h1.1.trans h2.1, fun _ hk => (h1.2 _ hk).trans (h2.2 _ hk)⟩

protected theorem PermStabilizing.mono (H : PermStabilizing lo hi as as')
    (hlo : lo' ≤ lo) (hhi : hi ≤ hi') : PermStabilizing lo' hi' as as' :=
  ⟨H.1, fun _ hk => H.2 _ <| mt (.imp (Nat.le_trans hlo) (Nat.le_trans · hhi)) hk⟩

theorem Vector.split_three (as : Vector α n) (h1 : lo ≤ hi) (h2 : hi ≤ n) :
    ∃ L₁ L₂ L₃, L₁.length = lo ∧ lo + L₂.length = hi ∧
      as.1.data = L₁ ++ L₂ ++ L₃ := by
  rw [← take_append_drop hi as.1.data, ← take_append_drop lo (as.1.data.take hi)]
  have lenhi {as : Vector α n} : length (take hi as.val.data) = hi :=
    length_take_of_le <| by rwa [← size, as.2]
  have {as : Vector α n} : lo ≤ length (take hi as.val.data) := lenhi.symm ▸ h1
  refine ⟨_, _, _, length_take_of_le this, ?_, rfl⟩
  rw [length_drop, Nat.add_sub_cancel' this, lenhi]

theorem PermStabilizing.list_perm (H : @PermStabilizing α n lo hi as as')
    {L₁ L₂ L₃} (eq : as.1.data = L₁ ++ L₂ ++ L₃)
    (h1 : L₁.length = lo) (h2 : lo + L₂.length = hi)
    {L₁' L₂' L₃'} (eq' : as'.1.data = L₁' ++ L₂' ++ L₃')
    (h1' : L₁'.length = lo) (h2' : lo + L₂'.length = hi) :
    L₁ = L₁' ∧ L₂ ~ L₂' ∧ L₃ = L₃' := by
  have H2 {k} h (hk : ¬(lo ≤ k ∧ k < hi)) :
      some (as.1.data.get ⟨k, _⟩) = some (as'.1.data.get ⟨k, _⟩) := congrArg _ (H.2 ⟨k, h⟩ hk)
  simp only [← get?_eq_get, eq, eq'] at H2
  have len := congrArg length eq; simp [as.2, ← Nat.add_assoc, h1, h2] at len
  have len' := congrArg length eq'; simp [as'.2, ← Nat.add_assoc, h1', h2'] at len'
  have lo_hi : lo ≤ hi := by rw [← h2]; apply Nat.le_add_right
  have hi_n : hi ≤ n := by rw [len]; apply Nat.le_add_right
  have eq₁ : L₁ = L₁' := by
    refine ext_get (h1' ▸ h1) fun i hi1 hi2 => Option.some_inj.1 ?_
    rw [← get?_eq_get, ← get?_eq_get]
    have i_lo := h1 ▸ hi1
    have := H2 (Nat.lt_of_lt_of_le i_lo (Nat.le_trans lo_hi hi_n)) fun h => Nat.not_le.2 i_lo h.1
    rwa [List.get?_append, List.get?_append hi1, List.get?_append, List.get?_append hi2] at this
      <;> (simp; omega)
  have eq₃ : L₃ = L₃' := by
    have len3 := h2 ▸ Nat.sub_eq_of_eq_add (Nat.add_comm .. ▸ len)
    have len3' := h2' ▸ Nat.sub_eq_of_eq_add (Nat.add_comm .. ▸ len')
    refine ext_get (len3 ▸ len3') fun i hi1 hi2 => Option.some_inj.1 ?_
    rw [← get?_eq_get, ← get?_eq_get]
    have i_hi := len3.symm ▸ hi1
    have := H2 (Nat.add_lt_of_lt_sub' i_hi) fun h => Nat.not_lt.2 (Nat.le_add_right ..) h.2
    rwa [List.get?_append_right, length_append, h1, h2, Nat.add_sub_cancel_left,
      List.get?_append_right, length_append, h1', h2', Nat.add_sub_cancel_left] at this
      <;> (simp; omega)
  refine ⟨eq₁, ?_, eq₃⟩
  exact (perm_append_left_iff _).1 <| (perm_append_right_iff _).1 <|
    eq₁ ▸ eq₃ ▸ eq ▸ eq' ▸ H.1

theorem swap_permStabilizing {as : Vector α n} {i j lo hi}
    (h_i : lo ≤ i.1 ∧ i.1 < hi) (h_j : lo ≤ j.1 ∧ j.1 < hi) :
    PermStabilizing lo hi (as.swap i j) as := by
  refine ⟨swap_perm .., fun k hk => .symm ?_⟩
  simp [Vector.get, Vector.swap, get_swap']; split <;> [skip; split]
  · next eq => rw [eq] at hk; cases hk h_i
  · next eq => rw [eq] at hk; cases hk h_j
  · rfl

theorem qpartition_maybeSwap_permStabilizing {lt : α → α → Bool} {as : Vector α n} {i j lo hi}
    (h_i : lo ≤ i.1 ∧ i.1 < hi) (h_j : lo ≤ j.1 ∧ j.1 < hi) :
    PermStabilizing lo hi (qpartition'.maybeSwap lt as i j) as := by
  simp [qpartition'.maybeSwap]; split <;> [apply swap_permStabilizing h_i h_j; rfl]

theorem qpartition_loop_permStabilizing
    (lt : α → α → Bool) (lo hi pivot) (as : Vector α n) {i j} (H) :
    PermStabilizing lo.1 (hi.1+1) (qpartition'.loop lt lo hi pivot as i j H).1 as := by
  have h_i : lo.1 ≤ i.1 ∧ i.1 < hi.1 + 1 := ⟨H.1, Nat.lt_succ.2 (Nat.le_trans H.2.1 H.2.2)⟩
  have h_j : lo.1 ≤ j.1 ∧ j.1 < hi.1 + 1 := ⟨Nat.le_trans H.1 H.2.1, Nat.lt_succ.2 H.2.2⟩
  have h_hi : lo.1 ≤ hi.1 ∧ hi.1 < hi.1 + 1 :=
    ⟨Nat.le_trans H.1 (Nat.le_trans H.2.1 H.2.2), Nat.lt_succ_self _⟩
  unfold qpartition'.loop; split; split <;> [split; skip]
  · exact (qpartition_loop_permStabilizing ..).trans (swap_permStabilizing h_i h_j)
  · apply qpartition_loop_permStabilizing
  · apply swap_permStabilizing (as := as) h_i h_hi
termination_by hi.1 - j

theorem qpartition_permStabilizing (as : Vector α n) (lt : α → α → Bool) {lo hi} (hle) :
    PermStabilizing lo.1 (hi.1+1) (qpartition' as lt lo hi hle).1 as :=
  have h_lo : lo.1 ≤ lo.1 ∧ lo.1 < hi.1 + 1 := ⟨Nat.le_refl _, Nat.lt_succ.2 hle⟩
  have h_hi : lo.1 ≤ hi.1 ∧ hi.1 < hi.1 + 1 := ⟨hle, Nat.lt_succ_self _⟩
  have h_mid : lo.1 ≤ (lo.1 + hi.1) / 2 ∧ (lo.1 + hi.1) / 2 < hi.1 + 1 := by omega
  (qpartition_loop_permStabilizing ..).trans <|
  (qpartition_maybeSwap_permStabilizing h_hi (by exact h_mid)).trans <|
  (qpartition_maybeSwap_permStabilizing h_lo h_hi).trans
  (qpartition_maybeSwap_permStabilizing h_lo h_mid)

theorem qsort_sort_permStabilizing (lt : α → α → Bool) (as : Vector α n) (lo hi) (hi_n : hi-1 < n) :
    PermStabilizing lo hi (qsort'.sort lt as lo ⟨hi-1, hi_n⟩) as := by
  unfold qsort'.sort; split <;> [split; rfl]
  next lo_hi _ _ mid h1 h2 eq =>
  have := ‹lo < hi - 1›; have := ‹mid ≤ hi - 1›
  refine
    ((qsort_sort_permStabilizing ..).mono (by omega) (Nat.le_refl _)).trans <|
    ((qsort_sort_permStabilizing ..).mono
      (Nat.le_refl _) (Nat.le_trans ‹_› (Nat.sub_le ..))).trans ?_
  let hi+1 := hi
  exact (‹_=_› ▸ qpartition_permStabilizing .. :)
termination_by hi - lo

theorem _root_.Array.qsort_perm' (as : Array α) (lt : α → α → Bool) {low high} :
    (as.qsort' lt low high).data ~ as.data := by
  unfold qsort'; split <;> [split <;> [skip; rfl]; rfl]
  exact (qsort_sort_permStabilizing (hi := high+1) ..).1

theorem _root_.Array.qsort_perm (as : Array α) (lt : α → α → Bool) :
    (as.qsort' lt).data ~ as.data := qsort_perm' ..

@[simp] theorem _root_.Array.qsort_size (as : Array α) (lt : α → α → Bool) :
    (as.qsort' lt low high).size = as.size := (qsort_perm' ..).length_eq

section sorted
variable (lt : α → α → Bool) (lt_asymm : ∀ {{a b}}, lt a b → ¬lt b a)
attribute [-simp] Bool.not_eq_true

theorem qpartition_loop_sorted {as as' : Vector α n}
    {L l₁ l₂ r M R}
    (eq : qpartition'.loop lt lo hi a as i j H = (as', pivot))
    (hL : L.length = lo.1)
    (hl₁ : lo.1 + l₁.length = i.1)
    (hl₂ : i.1 + l₂.length = j.1)
    (hr : j.1 + r.length = hi.1)
    (l₁_le : ∀ b ∈ l₁, ¬lt a b) (l₂_le : ∀ b ∈ l₂, ¬lt b a)
    (eq_as : as.1.data = L ++ l₁ ++ l₂ ++ r ++ a :: R)
    (eq_as' : as'.1.data = L ++ M ++ R) :
    ∃ l r, M = l ++ a :: r ∧ l.length = pivot.1.1 - lo.1 ∧
      (∀ b ∈ l, ¬lt a b) ∧ (∀ b ∈ r, ¬lt b a) := by
  revert eq; unfold qpartition'.loop; split; split
  · match r with | [] => simp at hr; omega | b::r => ?_
    rw [show get .. = _ from
      get_of_append (l₁ := L ++ l₁ ++ l₂) (a := b) (l₂ := r ++ a :: R)
        (by simp [eq_as]) (by simp [← Nat.add_assoc, hL, hl₁, hl₂])]
    split
    · let as₁ := as.swap i j
      obtain ⟨l₂', l₂p, eq_as₁⟩ : ∃ _, _ ∧ as₁.1.data = _ :=
        swap_of_append_right (A := L ++ l₁) (b := b) (C := r ++ a :: R)
          as.1 (by simp [hL, hl₁]) hl₂ (by simp [eq_as])
      refine fun eq => qpartition_loop_sorted (l₁ := l₁ ++ [b]) (r := r) (l₂ := l₂')
        eq hL ?_ ?_ ?_ ?_ (fun _ h => l₂_le _ (l₂p.mem_iff.1 h)) (eq_as₁.trans (by simp)) eq_as'
      · simp [← Nat.add_assoc, hl₁]
      · simp [Nat.add_right_comm, l₂p.length_eq, hl₂]
      · simp [Nat.add_right_comm, ← hr]; rfl
      · simp [or_imp, forall_and, eq_true l₁_le]; exact lt_asymm ‹_›
    · refine fun eq => qpartition_loop_sorted (l₂ := l₂ ++ [b]) (r := r)
        eq hL hl₁ ?_ ?_ l₁_le ?_ (by simp [eq_as]) eq_as'
      · simp [← Nat.add_assoc, hl₂]
      · simp [Nat.add_right_comm, ← hr]; rfl
      · simp [or_imp, forall_and, eq_true l₂_le]; assumption
  · cases r <;> simp at hr <;> [skip; omega]
    rintro ⟨⟩
    let as₁ := as.swap i hi
    obtain ⟨l₂', l₂p, eq_as₁⟩ : ∃ _, _ ∧ as₁.1.data = _ :=
      swap_of_append_right (A := L ++ l₁) (B := l₂) (b := a) (C := R)
        as.1 (by simp [hL, hl₁]) (by simp [hl₂, hr]) (by simp [eq_as])
    have := (List.append_left_inj _).1 <| eq_as'.symm.trans eq_as₁
    rw [List.append_assoc, List.append_right_inj] at this
    refine ⟨_, _, this, by simp [← hl₁, Nat.add_sub_cancel_left], l₁_le, ?_⟩
    exact fun _ h => l₂_le _ (l₂p.mem_iff.1 h)

theorem qpartition_sorted {as as' : Vector α n}
    (eq : qpartition' as lt lo hi H = (as', pivot))
    {L M R} (hlo : L.length = lo.1) (hhi : lo.1 + M.length = hi.1+1)
    (eq_as' : as'.1.data = L ++ M ++ R) :
    ∃ l a r, M = l ++ a :: r ∧ l.length = pivot.1.1 - lo.1 ∧
      (∀ b ∈ l, ¬lt a b) ∧ (∀ b ∈ r, ¬lt b a) := by
  let mid : Fin n := ⟨(lo.1 + hi) / 2, by omega⟩
  let as₁ := qpartition'.maybeSwap lt as lo mid
  let as₁ := qpartition'.maybeSwap lt as₁ lo hi
  let as₁ : Vector _ n := qpartition'.maybeSwap lt as₁ hi mid
  let a := as₁.get hi
  replace eq : qpartition'.loop lt lo hi a as₁ .. = (as', pivot) := eq
  have perm := eq ▸ qpartition_loop_permStabilizing lt lo hi a as₁ _
  obtain ⟨LM, _, R', eq_as₁, hhi', (rfl : a = _)⟩ := exists_of_get _
  obtain ⟨L', M', rfl, hlo'⟩ := exists_of_length_le (l := LM) (n := lo) (hhi' ▸ H)
  simp [hlo'] at hhi'
  obtain ⟨rfl, -, rfl⟩ := perm.list_perm (L₂' := M' ++ [a]) (L₃' := R')
    eq_as' hlo hhi (by simp [eq_as₁]) hlo' (by simp [← hhi', Nat.add_assoc])
  let ⟨l, h⟩ := qpartition_loop_sorted (l₁ := []) (l₂ := [])
    lt lt_asymm eq hlo rfl rfl hhi' (by simp) (by simp) (by simp [eq_as₁]) eq_as'
  exact ⟨l, _, h⟩

variable (le_trans : ∀ {{a b c}}, ¬lt a b → ¬lt b c → ¬lt a c)

theorem qsort_sorted_base {r} {M : List α} (hhi : lo + M.length = hi)
    (hn : ¬lo < hi - 1) : M.Pairwise r := by
  match M with
  | [] => exact .nil
  | [_] => apply pairwise_singleton
  | _::_::_ => exfalso; apply ‹¬_›; simp at hhi ⊢; omega

theorem qsort_sort_sorted (as : Vector α n)
    {L M R} (hlo : L.length = lo) (hhi : lo + M.length = hi) (hi_n : hi-1 < n) :
    (qsort'.sort lt as lo ⟨hi-1, hi_n⟩).1.data = L ++ M ++ R →
    M.Pairwise (fun a b => ¬lt b a) := by
  have lo_hi : lo ≤ hi := hhi ▸ hlo ▸ Nat.le_add_right ..
  unfold qsort'.sort; split
  · let hi+1 := hi; split; rename_i as₀ pivot h1 h2 eq
    replace h2 : pivot ≤ hi := h2
    have ⟨L₀, M₀, R₀, hlo₀, hhi₀, has₀⟩ := Vector.split_three as₀ lo_hi hi_n
    have ⟨l₁, a, r₁, hM₀, hl₁, hp1, hp2⟩ := qpartition_sorted lt lt_asymm eq hlo₀ hhi₀ has₀
    let pivot₁ : Fin n := ⟨↑pivot - 1, by omega⟩
    let as₁ := qsort'.sort lt as₀ lo pivot₁
    have ⟨L₂, l₂, arR₂, hlo₂, hhi₂, has₁⟩ :=
      Vector.split_three as₁ h1 (Nat.le_of_lt <| Nat.lt_of_le_of_lt h2 hi_n)
    have sort_l₂ := qsort_sort_sorted as₀ hlo₂ hhi₂ pivot₁.2 has₁
    let as₂ := qsort'.sort lt as₁ (pivot+1) ⟨hi, hi_n⟩
    have ⟨Lla₃, r₃, R₃, hp₃, hhi₃, has₂⟩ :=
      Vector.split_three as₂ (Nat.succ_le_succ h2) hi_n
    have sort_r₃ := qsort_sort_sorted as₁ hp₃ hhi₃ hi_n has₂
    obtain ⟨rfl, ll, rfl⟩ := (qsort_sort_permStabilizing ..).list_perm has₁ hlo₂ hhi₂
      (L₂' := l₁) (L₃' := a :: r₁ ++ R₀) (by simp [has₀, hM₀])
      hlo₀ (by simp [hlo₀, hl₁, Nat.add_sub_cancel' h1])
    obtain ⟨rfl, rr, rfl⟩ := (qsort_sort_permStabilizing ..).list_perm has₂ hp₃ hhi₃
      (L₁' := L₂ ++ l₂ ++ [a]) (L₂' := r₁) (L₃' := R₀) (by simp [has₁])
      (by simp [hlo₂, ← Nat.add_assoc, hhi₂])
      (by simpa [hM₀, ← ll.length_eq, hhi₂, Nat.succ_add, Nat.add_succ, ← Nat.add_assoc] using hhi₀)
    intro has₃; replace has₃ := has₂.symm.trans has₃
    obtain ⟨has₃', rfl⟩ := append_inj has₃ <| by
      simpa [hlo₂, hlo, hhi, hM₀, ll.length_eq, rr.length_eq] using hhi₀
    simp at has₃
    obtain ⟨rfl, has₃'⟩ := append_inj has₃ (hlo₂.trans hlo.symm)
    simp at has₃'; subst M
    simp only [pairwise_append, pairwise_cons, forall_mem_cons, rr.mem_iff, ll.mem_iff]
    exact ⟨sort_l₂, ⟨hp2, sort_r₃⟩, fun x hx =>
      ⟨hp1 _ hx, fun y hy => le_trans (hp2 _ hy) (hp1 _ hx)⟩⟩
  · exact fun _ => qsort_sorted_base hhi ‹¬_›
termination_by hi - lo

theorem qsort_sorted' (as : Array α)
    {L M R} (hlo : L.length = lo) (hhi : lo + M.length = hi) (hi_n : hi ≤ as.size) :
    (qsort' as lt lo (hi-1)).data = L ++ M ++ R → M.Pairwise (fun a b => ¬lt b a) := by
  unfold qsort'; split
  · split
    · refine qsort_sort_sorted lt (as := {..}) lt_asymm le_trans hlo hhi _
    · let hi+1 := hi; cases ‹¬_› hi_n
  · exact fun _ => qsort_sorted_base hhi ‹¬_›

theorem _root_.Array.qsort_sorted (as : Array α) :
    (as.qsort' lt).data.Pairwise (fun a b => ¬lt b a) :=
  qsort_sorted' lt lt_asymm le_trans as (L := []) (R := []) rfl (by simp) (Nat.le_refl _) (by simp)

end sorted
