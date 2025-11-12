/-
Copyright (c) 2014 Parikshit Khanna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Parikshit Khanna, Jeremy Avigad, Leonardo de Moura, Floris van Doorn, Mario Carneiro
-/
module

public import Batteries.Data.List.Basic
meta import Batteries.Tactic.Init

@[expose] public section

/-!
# List scan

Prove basic results about `List.scanl` and `List.scanr`.
-/

namespace List

/-! ### List.scanl -/

@[simp, grind =]
theorem length_scanl {f : β → α → β} (b : β) (l : List α) :
    length (scanl f b l) = l.length + 1 := by
  induction l generalizing b <;> simp_all

@[simp, grind =]
theorem scanl_nil {f : β → α → β} (b : β) : scanl f b [] = [b] :=
  rfl

@[simp, grind =]
theorem scanl_cons {f : β → α → β} : scanl f b (a :: l) = b :: scanl f (f b a) l := by
  simp only [scanl]

theorem scanl_singleton {f : β → α → β} : scanl f b [a] = [b, f b a] := by
  simp

@[simp]
theorem scanl_ne_nil {f : β → α → β} : scanl f b l ≠ [] := by
  cases l <;> simp

@[simp]
theorem scanl_iff_nil {f : β → α → β} (c : β) : scanl f b l = [c] ↔ c = b ∧ l = [] := by
  constructor <;> cases l <;> simp_all

@[simp, grind =]
theorem getElem_scanl {f : α → β → α} (h : i < (scanl f a l).length) :
    (scanl f a l)[i] = foldl f a (l.take i) := by
  induction l generalizing a i with
  | nil => simp
  | cons _ _ ih => cases i <;> simp [ih]

@[grind =]
theorem getElem?_scanl {f : α → β → α} :
    (scanl f a l)[i]? = if i ≤ l.length then some (foldl f a (l.take i)) else none := by
  grind

@[grind _=_]
theorem take_scanl {f : α → β → α} (a : α) (l : List β) (i : Nat) :
    (scanl f a l).take (i + 1) = scanl f a (l.take i) := by
  induction l generalizing a i with
  | nil => simp
  | cons _ _ ih => cases i <;> simp [ih]

theorem getElem?_scanl_zero {f : β → α → β} : (scanl f b l)[0]? = some b := by
  simp

theorem getElem_scanl_zero {f : β → α → β} : (scanl f b l)[0] = b := by
  simp

@[simp]
theorem head_scanl {f : β → α → β} (h : scanl f b l ≠ []) :
    (scanl f b l).head h = b := by grind

theorem getLast_scanl {f : β → α → β} (h : scanl f b l ≠ []) :
    (scanl f b l).getLast h = foldl f b l := by
  induction l generalizing b
  case nil => simp
  case cons head tail ih => simp [getLast_cons, scanl_ne_nil, ih]

theorem getLast?_scanl {f : β → α → β} : (scanl f b l).getLast? = some (foldl f b l) := by
  simp [getLast?]
  split
  · exact absurd ‹_› scanl_ne_nil
  · simp [←‹_›, getLast_scanl]

theorem getElem?_succ_scanl {f : β → α → β} : (scanl f b l)[i + 1]? =
    (scanl f b l)[i]?.bind fun x => l[i]?.map fun y => f x y := by
  induction l generalizing b i with
  | nil => simp
  | cons _ _ ih => cases i <;> simp [ih]

theorem getElem_succ_scanl {f : β → α → β} (h : i + 1 < (scanl f b l).length) :
    (scanl f b l)[i + 1] = f (l.scanl f b)[i] (l[i]'(by grind)) := by
  induction i generalizing b l with
  | zero => cases l <;> simp at h ⊢
  | succ _ ih => cases l <;> simp [ih] at h ⊢

theorem scanl_append {f : β → α → β} (l₁ l₂ : List α) :
    scanl f b (l₁ ++ l₂) = scanl f b l₁ ++ (scanl f (foldl f b l₁) l₂).tail := by
  induction l₁ generalizing b
  case nil => cases l₂ <;> simp
  case cons head tail ih => simp [ih]

theorem scanl_map {f : β → γ → β} {g : α → γ} (b : β) (l : List α) :
    scanl f b (l.map g) = scanl (fun acc x => f acc (g x)) b l := by
  induction l generalizing b
  case nil => simp
  case cons head tail ih => simp [ih]

/-! ### List.scanr -/

@[simp, grind =]
theorem scanr_nil {f : α → β → β} (b : β) : scanr f b [] = [b] :=
  rfl

@[simp]
theorem scanr_ne_nil {f : α → β → β} : scanr f b l ≠ [] := by
  simp [scanr]

@[simp, grind =]
theorem scanr_cons {f : α → β → β} :
    scanr f b (a :: l) = foldr f b (a :: l) :: scanr f b l := by
  simp only [scanr, foldr, cons.injEq, and_true]
  induction l generalizing a with
  | nil => rfl
  | cons _ _ ih => simp only [foldr, ih]

theorem scanr_singleton {f : α → β → β} : scanr f b [a] = [f a b, b] := by
  simp

@[simp]
theorem scanr_iff_nil {f : α → β → β} (c : β) : scanr f b l = [c] ↔ c = b ∧ l = [] := by
  constructor <;> cases l <;> simp_all

@[simp, grind =]
theorem length_scanr {f : α → β → β} (b : β) (l : List α) :
    length (scanr f b l) = l.length + 1 := by induction l <;> simp_all

theorem scanr_append {f : α → β → β} (l₁ l₂ : List α) :
    scanr f b (l₁ ++ l₂) = (scanr f (foldr f b l₂) l₁) ++ (scanr f b l₂).tail := by
  induction l₁ <;> induction l₂ <;> simp [*]

@[simp]
theorem head_scanr {f : α → β → β} (h : scanr f b l ≠ []) :
    (scanr f b l).head h = foldr f b l := by cases l <;> simp

theorem getLast_scanr {f : α → β → β} (h : scanr f b l ≠ []) :
    (scanr f b l).getLast h = b := by
  induction l
  case nil => simp
  case cons head tail ih => simp [getLast_cons, scanr_ne_nil, ih]

theorem getLast?_scanr {f : α → β → β} : (scanr f b l).getLast? = some b := by
  simp [getLast?]
  split
  · exact absurd ‹_› scanr_ne_nil
  · simp [←‹_›, getLast_scanr]

theorem tail_scanr {f : α → β → β} (h : 0 < l.length) :
    (scanr f b l).tail = scanr f b l.tail := by induction l <;> simp_all

@[grind _=_]
theorem drop_scanr {f : α → β → β} (h : i ≤ l.length) :
    (scanr f b l).drop i = scanr f b (l.drop i) := by
  induction i generalizing l with
  | zero => simp
  | succ => cases l <;> simp_all

@[simp, grind =]
theorem getElem_scanr {f : α → β → β} (h : i < (scanr f b l).length) :
    (scanr f b l)[i] = foldr f b (l.drop i) := by
  induction l generalizing i with
  | nil => simp
  | cons _ _ ih => cases i <;> simp [ih] at h ⊢

@[grind =]
theorem getElem?_scanr {f : α → β → β} (h : i < l.length + 1) :
    (scanr f b l)[i]? = if i < l.length + 1 then some (foldr f b (l.drop i)) else none := by
  grind

theorem getElem_scanr_zero {f : α → β → β} : (scanr f b l)[0] = foldr f b l := by
  simp

theorem getElem?_scanr_zero {f : α → β → β} : (scanr f b l)[0]? = some (foldr f b l) := by
  simp

theorem getElem?_scanr_of_lt {f : α → β → β} (h : i < l.length + 1) :
    (scanr f b l)[i]? = some (foldr f b (l.drop i)) := by
  simp [h]

theorem scanr_map {f : α → β → β} {g : γ → α} (b : β) (l : List γ) :
    scanr f b (l.map g) = scanr (fun x acc => f (g x) acc) b l := by
  suffices ∀ l, foldr f b (l.map g) = foldr (fun x acc => f (g x) acc) b l from by
    induction l generalizing b <;> simp [*]
  intro l
  induction l <;> simp [*]

@[simp, grind =]
theorem scanl_reverse {f : β → α → β} (b : β) (l : List α) :
    scanl f b l.reverse = reverse (scanr (flip f) b l) := by
  induction l generalizing b
  case nil => rfl
  case cons head tail ih => simp [scanl_append, ih]; rfl

@[simp, grind =]
theorem scanr_reverse {f : α → β → β} (b : β) (l : List α) :
    scanr f b l.reverse = reverse (scanl (flip f) b l) := by
  induction l generalizing b
  case nil => rfl
  case cons head tail ih => simp [scanr_append, ih]; rfl


/-! ### partialSums -/

@[simp, grind =]
theorem partialSums_nil : partialSums [] = [0] := rfl

private theorem scanl_add (a : Nat) (l : List Nat) :
    scanl (·+·) a l = (scanl (·+·) 0 l).map (a + ·) := by
  induction l generalizing a with
  | nil => rfl
  | cons b l ih =>
    simp only [scanl, List.map_cons, Nat.add_zero, Nat.zero_add]
    rw [ih (a + b), ih b]
    simp only [List.map_map]
    congr 1
    ext x
    simp [Function.comp_def, Nat.add_assoc]

theorem partialSums_cons (a : Nat) (l : List Nat) :
    partialSums (a :: l) = 0 :: (partialSums l).map (a + ·) := by
  simp only [partialSums, scanl, Nat.zero_add]
  rw [scanl_add]

@[simp, grind =]
theorem length_partialSums (l : List Nat) :
    (partialSums l).length = l.length + 1 := by
  simp [partialSums, length_scanl]

-- Helper: foldl and foldr are equivalent for addition on Nat
private theorem foldl_add_eq_foldr_add (l : List Nat) (a : Nat) :
    foldl (·+·) a l = a + foldr (·+·) 0 l := by
  induction l generalizing a with
  | nil => simp
  | cons b l ih =>
    simp [ih]
    omega

@[simp, grind =]
theorem getElem_partialSums (l : List Nat) (i : Nat) (h : i < (partialSums l).length) :
    (partialSums l)[i] = (l.take i).sum := by
  simp only [partialSums, getElem_scanl, List.sum]
  rw [foldl_add_eq_foldr_add]
  simp

@[grind =]
theorem getElem?_partialSums (l : List Nat) (i : Nat) :
    (partialSums l)[i]? = if i ≤ l.length then some (l.take i).sum else none := by
  simp [partialSums, getElem?_scanl, List.sum]
  split <;> rename_i h
  · rw [foldl_add_eq_foldr_add]; simp
  · rfl

@[simp, grind =]
theorem take_partialSums (l : List Nat) (i : Nat) :
    l.partialSums.take (i + 1) = (l.take i).partialSums := by
  simp [partialSums, take_scanl]

/-! ### flatten -/

theorem length_flatten_mem_partialSums_map_length (L : List (List α)) :
    L.flatten.length ∈ (L.map length).partialSums := by
  induction L with
  | nil => simp
  | cons l L ih =>
    simp [flatten_cons, partialSums_cons]
    right
    simpa using ih

theorem getElem_flatten_aux₁ (L : List (List α)) (i : Nat) (h : i < L.flatten.length) :
    (L.map length).partialSums.findIdx (· > i) - 1 < L.length := by
  have := findIdx_lt_length_of_exists (xs := (L.map length).partialSums) (p := fun x => decide (x > i))
  specialize this ⟨L.flatten.length,
    length_flatten_mem_partialSums_map_length L, by grind⟩
  simp at this
  simp
  have : 0 < findIdx (fun x => decide (i < x)) (map length L).partialSums := by
    by_contra w
    simp at w
  omega

theorem getElem_flatten_aux₂ (L : List (List α)) (i : Nat) (h : i < L.flatten.length) :
    let j := (L.map length).partialSums.findIdx (· > i) - 1
    have hj : j < L.length := getElem_flatten_aux₁ L i h
    let k := i - (L.take j).flatten.length
    k < L[j].length := sorry

/--
Indexing into a flattened list: `L.flatten[i]` equals `L[j][k]` where
`j` is the sublist index and `k` is the offset within that sublist.

The indices are computed as:
- `j` is one less than where the cumulative sum first exceeds `i`
- `k` is `i` minus the total length of the first `j` sublists

This theorem states that these indices are in range and the equality holds.
-/
theorem getElem_flatten (L : List (List α)) (i : Nat) (h : i < L.flatten.length) :
    L.flatten[i] =
      let j := (L.map length).partialSums.findIdx (· > i) - 1
      have hj : j < L.length := getElem_flatten_aux₁ L i h
      let k := i - (L.take j).flatten.length
      have hk : k < L[j].length := getElem_flatten_aux₂ L i h
      L[j][k] := by
  induction L generalizing i with
  | nil => simp at h
  | cons l L ih =>
    simp only [flatten_cons, getElem_append]
    split <;> rename_i h'
    · have : findIdx (fun x => decide (x > i)) (map length (l :: L)).partialSums = 1 := by
        simp [partialSums_cons, findIdx_cons]
        rw [findIdx_eq] <;> grind
      simp only [this]
      simp
    · rw [ih]
      have : findIdx (fun x => decide (x > i)) (map length (l :: L)).partialSums =
          findIdx (fun x => decide (x > i - l.length)) (map length L).partialSums + 1 := by
        simp [partialSums_cons, findIdx_cons, Function.comp_def]
        congr
        funext x
        grind
      simp only [this]
      simp only [getElem_cons]
      split <;> rename_i h''
      · simp [findIdx_eq] at h''
      · congr 1
        rw [take_cons]
        · simp
          omega
        · simp

/--
Taking the first `i` elements of a flattened list
can be expressed as the flattening of the first `j` complete sublists, plus the first
`k` elements of the `j`-th sublist.

The indices are computed as:
- `j` is one less than where the cumulative sum first exceeds `i`
- `k` is `i` minus the total length of the first `j` sublists
-/
theorem take_flatten (L : List (List α)) (i : Nat) :
    let j := (L.map length).partialSums.findIdx (· > i) - 1
    let k := i - (L.take j).flatten.length
    L.flatten.take i = (L.take j).flatten ++ (L[j]?.getD []).take k := by
  sorry
