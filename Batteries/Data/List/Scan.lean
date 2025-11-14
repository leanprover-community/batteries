/-
Copyright (c) 2014 Parikshit Khanna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Parikshit Khanna, Jeremy Avigad, Leonardo de Moura, Floris van Doorn, Mario Carneiro
-/
module

public import Batteries.Data.List.Basic
public import Batteries.Data.List.Lemmas

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

/-! ### partialSums/partialProd -/

@[simp, grind =]
theorem length_partialSums [Add α] [Zero α] {l : List α} :
    l.partialSums.length = l.length + 1 := by
  simp [partialSums]

@[simp, grind =]
theorem partialSums_nil [Add α] [Zero α] : ([] : List α).partialSums = [0] := rfl

theorem partialSums_cons [Add α] [Zero α] [Std.Associative (α := α) (· + ·)]
    [Std.LawfulIdentity (α := α) (· + ·) 0] {l : List α} :
    (a :: l).partialSums = 0 :: l.partialSums.map (a + ·) := by
  simp only [partialSums, scanl, Std.LawfulLeftIdentity.left_id, cons.injEq]
  induction l generalizing a with
  | nil =>
    simp only [Std.LawfulRightIdentity.right_id, scanl, map_cons, map_nil]
  | cons b l ih =>
    simp [Std.LawfulLeftIdentity.left_id, Std.LawfulRightIdentity.right_id]
    rw [ih (a := b), ih (a := a + b), map_map]
    congr; funext; simp [Std.Associative.assoc]

@[simp, grind =]
theorem getElem_partialSums [Add α] [Zero α] [Std.Associative (α := α) (· + ·)]
    [Std.LawfulIdentity (α := α) (· + ·) 0] {l : List α} (h : i < l.partialSums.length) :
    l.partialSums[i] = (l.take i).sum := by
  simp [partialSums, sum_eq_foldl]

@[simp, grind =]
theorem getElem?_partialSums [Add α] [Zero α] [Std.Associative (α := α) (· + ·)]
    [Std.LawfulIdentity (α := α) (· + ·) 0] {l : List α} (h : i < l.partialSums.length) :
    l.partialSums[i]? = if i ≤ l.length then some (l.take i).sum else none := by
  split <;> grind

@[simp, grind =]
theorem take_partialSums [Add α] [Zero α] {l : List α} :
    l.partialSums.take (i+1) = (l.take i).partialSums := by
  simp [partialSums, take_scanl]
