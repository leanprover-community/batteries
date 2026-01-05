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

Prove basic results about `List.scanl`, `List.scanr`, `List.scanlM` and `List.scanrM`.
-/

namespace List

/-! ### `List.scanlM` and `List.scanrM` -/


@[local simp]
theorem scanAuxM.go_eq_append_map [Monad m] [LawfulMonad m] {f : α → β → m α} :
  go f xs last acc = (· ++ acc) <$> scanAuxM f last xs := by
  unfold scanAuxM
  induction xs generalizing last acc with
  | nil => simp [scanAuxM.go]
  | cons _ _ ih => simp [scanAuxM.go, ih (acc := last :: acc), ih (acc := [last])]

theorem scanAuxM_nil [Monad m] {f : α → β → m α} :
    scanAuxM f init [] = return [init] := rfl

theorem scanAuxM_cons [Monad m] [LawfulMonad m] {f : α → β → m α} :
    scanAuxM f init (x :: xs) = return (← scanAuxM f (← f init x) xs) ++ [init] := by
  rw [scanAuxM, scanAuxM.go]
  simp

@[simp, grind =]
theorem scanlM_nil [Monad m] [LawfulMonad m] {f : α → β → m α} :
    scanlM f init [] = return [init] := by
  simp [scanlM, scanAuxM_nil]


@[simp, grind =]
theorem scanlM_cons [Monad m] [LawfulMonad m] {f : α → β → m α} :
    scanlM f init (x :: xs) = return init :: (← scanlM f (← f init x) xs) := by
  simp [scanlM, scanAuxM_cons]


@[simp, grind =]
theorem scanrM_concat [Monad m] [LawfulMonad m] {f : α → β → m β} :
    scanrM f init (xs ++ [x]) = return (← scanrM f (← f x init) xs) ++ [init] := by
  simp [scanrM, flip, scanAuxM_cons]

@[simp, grind =]
theorem scanrM_nil [Monad m] {f : α → β → m β} :
    scanrM f init [] = return [init] := rfl

theorem scanlM_eq_scanrM_reverse [Monad m] {f : β → α → m β} {init : β} {as : List α} :
    scanlM f init as = reverse <$> (scanrM (flip f) init as.reverse) := by
  simp only [scanrM, reverse_reverse]
  rfl

theorem scanrM_eq_scanlM_reverse [Monad m] [LawfulMonad m]
    {f : α → β → m β}{init : β} {as : List α} :
    scanrM f init as = reverse <$> (scanlM (flip f) init as.reverse) := by
  simp only [scanlM_eq_scanrM_reverse, reverse_reverse, id_map', Functor.map_map]
  rfl

@[simp, grind =]
theorem scanrM_reverse [Monad m] [LawfulMonad m] {f : α → β → m β} {init : β} {as : List α} :
    scanrM f init as.reverse = reverse <$> (scanlM (flip f) init as) := by
  grind [scanrM_eq_scanlM_reverse]

@[simp, grind =]
theorem scanlM_reverse [Monad m] {f : β → α → m β} {init : β} {as : List α} :
    scanlM f init as.reverse = reverse <$> (scanrM (flip f) init as) := by
  grind [scanlM_eq_scanrM_reverse]


theorem scanlM_pure [Monad m] [LawfulMonad m] {f: β → α → β} {init: β} {as : List α} :
    as.scanlM (m := m) (pure <| f · ·) init = pure (as.scanl f init) := by
  induction as generalizing init with simp_all [scanlM_cons, scanl]

theorem scanrM_pure [Monad m] [LawfulMonad m] {f : α → β → β} {init : β} {as : List α} :
    as.scanrM (m := m) (pure <| f · · ) init = pure (as.scanr f init) := by
  simp only [scanrM_eq_scanlM_reverse]
  unfold flip
  simp only [scanlM_pure, map_pure, scanr,  scanrM_eq_scanlM_reverse]
  rfl

theorem idRun_scanlM {f : β → α → Id β} {init : β} {as : List α} :
    (as.scanlM f init).run = as.scanl (f · · |>.run) init :=
  scanlM_pure

theorem idRun_scanrM {f : α → β → Id β} {init : β} {as : List α} :
    (as.scanrM f init).run = as.scanr (f · · |>.run) init :=
  scanrM_pure

@[simp, grind =]
theorem scanlM_map [Monad m] [LawfulMonad m]
    {f : α₁ → α₂ } {g: β → α₂ → m β} {as : List α₁} {init : β} :
    (as.map f).scanlM g init = as.scanlM (g · <| f ·) init := by
  induction as generalizing g init with grind

@[simp, grind =]
theorem scanrM_map [Monad m] [LawfulMonad m]
    {f : α₁ → α₂ } {g: α₂ → β → m β} {as : List α₁} {init : β} :
    (as.map f).scanrM g init = as.scanrM (fun a b => g (f a) b) init := by
  simp only [← map_reverse, scanlM_map, scanrM_eq_scanlM_reverse]
  rfl


/-! ### `List.scanl` and `List.scanr` -/

@[simp]
theorem length_scanl {f : β → α → β} (init : β) (as : List α) :
    length (scanl f init as) = as.length + 1 := by
  induction as generalizing init <;> simp_all [scanl, pure, bind, Id.run]

grind_pattern length_scanl => scanl f init as

@[simp, grind =]
theorem scanl_nil {f : β → α → β} (b : β) : scanl f b [] = [b] := by simp [scanl]

@[simp, grind =]
theorem scanl_cons {f : β → α → β} :
    scanl f b (a :: l) = b :: scanl f (f b a) l := by
  simp [scanl]

theorem scanl_singleton {f : β → α → β} : scanl f b [a] = [b, f b a] := by
  simp

@[simp]
theorem scanl_ne_nil {f : β → α → β} : scanl f b l ≠ [] := by
  cases l <;> simp

-- This pattern can be removed after moving to a lean version containing
-- https://github.com/leanprover/lean4/pull/11760
local grind_pattern List.eq_nil_of_length_eq_zero => l.length where
  guard l.length = 0

@[simp]
theorem scanl_iff_nil {f : β → α → β} (c : β) : scanl f b l = [c] ↔ c = b ∧ l = [] := by
  grind

@[simp, grind =]
theorem getElem_scanl {f : α → β → α} (h : i < (scanl f a l).length) :
    (scanl f a l)[i] = foldl f a (l.take i) := by
  induction l generalizing a i with grind [cases Nat]

@[grind =]
theorem getElem?_scanl {f : α → β → α} :
    (scanl f a l)[i]? = if i ≤ l.length then some (foldl f a (l.take i)) else none := by
  grind

@[grind _=_]
theorem take_scanl {f : β → α → β} (init : β) (as : List α) (i : Nat) :
    (scanl f init as).take (i + 1) = scanl f init (as.take i) := by
  induction as generalizing init i with grind [cases Nat]

theorem getElem?_scanl_zero {f : β → α → β} : (scanl f b l)[0]? = some b := by
  simp

theorem getElem_scanl_zero {f : β → α → β} : (scanl f b l)[0] = b := by
  simp

@[simp]
theorem head_scanl {f : β → α → β} (h : scanl f b l ≠ []) : (scanl f b l).head h = b := by
  grind

theorem getLast_scanl {f : β → α → β} (h : scanl f b l ≠ []) :
    (scanl f b l).getLast h = foldl f b l := by
  grind

theorem getLast?_scanl {f : β → α → β} : (scanl f b l).getLast? = some (foldl f b l) := by
  grind

@[grind =]
theorem tail_scanl {f : β → α → β} (h : 0 < l.length) :
    (scanl f b l).tail = scanl f (f b (l.head (by grind))) l.tail := by
  induction l with grind

theorem getElem?_succ_scanl {f : β → α → β} :
    (scanl f b l)[i + 1]? = (scanl f b l)[i]?.bind fun x => l[i]?.map fun y => f x y := by
  grind [List.take_add_one] -- TODO: should this be a global grind pattern?

theorem getElem_succ_scanl {f : β → α → β} (h : i + 1 < (scanl f b l).length) :
    (scanl f b l)[i + 1] = f (l.scanl f b)[i] (l[i]'(by grind)) := by
  grind [List.take_add_one]

@[grind =]
theorem scanl_append {f : β → α → β} (l₁ l₂ : List α) :
    scanl f b (l₁ ++ l₂) = scanl f b l₁ ++ (scanl f (foldl f b l₁) l₂).tail := by
  induction l₁ generalizing b
  case nil => cases l₂ <;> simp
  case cons head tail ih => simp [ih]

@[grind =]
theorem scanl_map {f : β → γ → β} {g : α → γ} (init : β) (as : List α) :
    scanl f init (as.map g) = scanl (fun acc x => f acc (g x)) init as := by
  induction as generalizing init with grind

theorem scanl_eq_scanr_reverse  {f : β → α → β} {init : β} {as : List α} :
    scanl f init as = reverse (scanr (flip f) init as.reverse) := by
  simp only [scanl, scanr, Id.run, scanrM_reverse, Functor.map, reverse_reverse]
  rfl

theorem scanr_eq_scanl_reverse  {f : α → β → β} {init : β} {as : List α} :
    scanr f init as = reverse (scanl (flip f) init as.reverse) := by
  simp only [scanl_eq_scanr_reverse, reverse_reverse]
  rfl

@[simp, grind =]
theorem scanr_nil {f : α → β → β} (b : β) : scanr f b [] = [b] := by simp [scanr]


@[simp, grind =]
theorem scanr_cons {f : α → β → β} :
    scanr f b (a :: l) = foldr f b (a :: l) :: scanr f b l := by
  simp only [scanr_eq_scanl_reverse, reverse_cons, scanl_append]
  unfold flip
  simp


@[simp]
theorem scanr_ne_nil {f : α → β → β} : scanr f b l ≠ [] := by cases l <;> simp

theorem scanr_singleton {f : α → β → β} : scanr f b [a] = [f a b, b] := by
  simp

@[simp]
theorem length_scanr {f : α → β → β} (init : β) (as : List α) :
    length (scanr f init as) = as.length + 1 := by induction as <;> simp_all

grind_pattern length_scanr => scanr f init as

@[simp]
theorem scanr_iff_nil {f : α → β → β} (c : β) : scanr f b l = [c] ↔ c = b ∧ l = [] := by
  grind

@[grind =]
theorem scanr_append {f : α → β → β} (l₁ l₂ : List α) :
    scanr f b (l₁ ++ l₂) = (scanr f (foldr f b l₂) l₁) ++ (scanr f b l₂).tail := by
  induction l₁ <;> induction l₂ <;> simp [*]

@[simp]
theorem head_scanr {f : α → β → β} (h : scanr f b l ≠ []) :
    (scanr f b l).head h = foldr f b l := by
  cases l <;> grind

@[grind =]
theorem getLast_scanr {f : α → β → β} (h : scanr f b l ≠ []) :
    (scanr f b l).getLast h = b := by
  induction l with grind [scanr_ne_nil]

theorem getLast?_scanr {f : α → β → β} : (scanr f b l).getLast? = some b := by
  simp only [getLast?]
  grind

@[grind =]
theorem tail_scanr {f : α → β → β} (h : 0 < l.length) :
    (scanr f b l).tail = scanr f b l.tail := by induction l with simp_all

@[grind _=_]
theorem drop_scanr {f : α → β → β} (h : i ≤ l.length) :
    (scanr f b l).drop i = scanr f b (l.drop i) := by
  induction i generalizing l with grind [cases List]

@[simp, grind =]
theorem getElem_scanr {f : α → β → β} (h : i < (scanr f b l).length) :
    (scanr f b l)[i] = foldr f b (l.drop i) := by
  induction l generalizing i with grind [cases Nat]

@[grind =]
theorem getElem?_scanr {f : α → β → β} :
    (scanr f b l)[i]? = if i < l.length + 1 then some (foldr f b (l.drop i)) else none := by
  grind

theorem getElem_scanr_zero {f : α → β → β} : (scanr f b l)[0] = foldr f b l := by
  simp

theorem getElem?_scanr_zero {f : α → β → β} :
    (scanr f b l)[0]? = some (foldr f b l) := by
  simp

theorem getElem?_scanr_of_lt {f : α → β → β} (h : i < l.length + 1) :
    (scanr f b l)[i]? = some (foldr f b (l.drop i)) := by
  simp [h]

@[grind =]
theorem scanr_map {f : α → β → β} {g : γ → α} (b : β) (l : List γ) :
    scanr f b (l.map g) = scanr (fun x acc => f (g x) acc) b l := by
  suffices ∀ l, foldr f b (l.map g) = foldr (fun x acc => f (g x) acc) b l from by
    induction l generalizing b with simp [*]
  intro l
  induction l with simp [*]

@[simp, grind =]
theorem scanl_reverse {f : β → α → β} (init : β) (as : List α) :
    scanl f init as.reverse = reverse (scanr (flip f) init as) := by
  induction as generalizing init <;> simp_all [scanl_append]
  rfl

/-! ### partialSums/partialProd -/

@[simp, grind =]
theorem length_partialSums [Add α] [Zero α] {l : List α} :
    l.partialSums.length = l.length + 1 := by
  simp [partialSums]

@[simp]
theorem partialSums_ne_nil [Add α] [Zero α] {l : List α} :
    l.partialSums ≠ [] := by simp [ne_nil_iff_length_pos]

@[simp, grind =]
theorem partialSums_nil [Add α] [Zero α] : ([] : List α).partialSums = [0] := by
  simp [partialSums]

theorem partialSums_cons [Add α] [Zero α] [Std.Associative (α := α) (· + ·)]
    [Std.LawfulIdentity (α := α) (· + ·) 0] {l : List α} :
    (a :: l).partialSums = 0 :: l.partialSums.map (a + ·) := by
  simp only [partialSums, scanl_cons, Std.LawfulLeftIdentity.left_id, cons.injEq]
  induction l generalizing a with
  | nil =>
    simp only [Std.LawfulRightIdentity.right_id, scanl_nil, map_cons, map_nil]
  | cons b l ih =>
    simp [Std.LawfulLeftIdentity.left_id, Std.LawfulRightIdentity.right_id]
    rw [ih (a := b), ih (a := a + b), map_map]
    congr; funext; simp [Std.Associative.assoc]

theorem partialSums_append [Add α] [Zero α] [Std.Associative (α := α) (· + ·)]
    [Std.LawfulIdentity (α := α) (· + ·) 0] {l₁ l₂ : List α} :
    (l₁ ++ l₂).partialSums = l₁.partialSums ++ l₂.partialSums.tail.map (l₁.sum + · ) := by
  induction l₁ generalizing l₂ with
  | nil => cases l₂ <;> simp [partialSums, Std.LawfulLeftIdentity.left_id]
  | cons _ _ ih =>
    simp only [cons_append, partialSums_cons, ih, map_tail, map_append, map_map, sum_cons,
      cons.injEq, append_cancel_left_eq, true_and]
    congr 2; funext; simp [Std.Associative.assoc]

@[simp, grind =]
theorem getElem_partialSums [Add α] [Zero α] [Std.Associative (α := α) (· + ·)]
    [Std.LawfulIdentity (α := α) (· + ·) 0] {l : List α} (h : i < l.partialSums.length) :
    l.partialSums[i] = (l.take i).sum := by
  simp [partialSums, sum_eq_foldl]

@[simp, grind =]
theorem getElem?_partialSums [Add α] [Zero α] [Std.Associative (α := α) (· + ·)]
    [Std.LawfulIdentity (α := α) (· + ·) 0] {l : List α} :
    l.partialSums[i]? = if i ≤ l.length then some (l.take i).sum else none := by
  split <;> grind

@[simp, grind =]
theorem take_partialSums [Add α] [Zero α] {l : List α} :
    l.partialSums.take (i+1) = (l.take i).partialSums := by
  simp [partialSums, take_scanl]

@[simp, grind =]
theorem length_partialProds [Mul α] [One α] {l : List α} :
    l.partialProds.length = l.length + 1 := by
  simp [partialProds]

@[simp, grind =]
theorem partialProds_nil [Mul α] [One α]
  : ([] : List α).partialProds = [1]
  := by simp [partialProds]

theorem partialProds_cons [Mul α] [One α] [Std.Associative (α := α) (· * ·)]
    [Std.LawfulIdentity (α := α) (· * ·) 1] {l : List α} :
    (a :: l).partialProds = 1 :: l.partialProds.map (a * ·) := by
  simp only [partialProds, scanl_cons, Std.LawfulLeftIdentity.left_id, cons.injEq]
  induction l generalizing a with
  | nil =>
    simp only [Std.LawfulRightIdentity.right_id, scanl_nil, map_cons, map_nil]
  | cons b l ih =>
    simp [Std.LawfulLeftIdentity.left_id, Std.LawfulRightIdentity.right_id]
    rw [ih (a := b), ih (a := a * b), map_map]
    congr; funext; simp [Std.Associative.assoc]

theorem partialProds_append [Mul α] [One α] [Std.Associative (α := α) (· * ·)]
    [Std.LawfulIdentity (α := α) (· * ·) 1] {l₁ l₂ : List α} :
    (l₁ ++ l₂).partialProds = l₁.partialProds ++ l₂.partialProds.tail.map (l₁.prod * · ) := by
  induction l₁ generalizing l₂ with
  | nil => cases l₂ <;> simp [partialProds, Std.LawfulLeftIdentity.left_id]
  | cons _ _ ih =>
    simp only [cons_append, partialProds_cons, ih, map_tail, map_append, map_map, prod_cons,
      cons.injEq, append_cancel_left_eq, true_and]
    congr 2; funext; simp [Std.Associative.assoc]

@[simp, grind =]
theorem getElem_partialProds [Mul α] [One α] [Std.Associative (α := α) (· * ·)]
    [Std.LawfulIdentity (α := α) (· * ·) 1] {l : List α} (h : i < l.partialProds.length) :
    l.partialProds[i] = (l.take i).prod := by
  simp [partialProds, prod_eq_foldl]

@[simp, grind =]
theorem getElem?_partialProds [Mul α] [One α] [Std.Associative (α := α) (· * ·)]
    [Std.LawfulIdentity (α := α) (· * ·) 1] {l : List α} :
    l.partialProds[i]? = if i ≤ l.length then some (l.take i).prod else none := by
  split <;> grind

@[simp, grind =]
theorem take_partialProds [Mul α] [One α] {l : List α} :
    l.partialProds.take (i+1) = (l.take i).partialProds := by
  simp [partialProds, take_scanl]
