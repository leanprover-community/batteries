/-
Copyright (c) 2014 Parikshit Khanna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chad Sharp
-/
module

public import Batteries.Data.Array.Basic
public import Batteries.Data.Array.Lemmas
import Batteries.Data.List.Scan

public section

/-!
# Array

Prove basic results about `Array.scanl`, `Array.scanr`, `Array.scanlM` and `Array.scanrM`.
-/
namespace Array

theorem scanlM.loop_toList [Monad m] [LawfulMonad m]
    {f : β → α → m β} {stop : Nat} (h : stop ≤ as.size) :
    scanlM.loop f init as start stop h acc =
      return acc.toList
               ++ (← as.toList.drop start
                  |>.take (stop - start)
                  |>.scanlM f init)
               |>.toArray := by
  induction h_ind : stop - start generalizing start acc init with
  | zero =>
    unfold scanlM.loop
    simp [show ¬(start < stop) by omega, ← Array.toList_push]
  | succ n ih =>
    unfold scanlM.loop
    rw [List.drop_eq_getElem_cons (by simp; omega)]
    simp [show start < stop by omega, show stop - (start + 1) = n by omega, ih]

theorem toArray_scanlM_toList [Monad m] [LawfulMonad m] {f : β → α → m β} {as : Array α} :
    List.toArray <$> as.toList.scanlM f init = as.scanlM f init := by
  simp [scanlM, Array.scanlM.loop_toList, ←Array.length_toList]

@[simp, grind =]
theorem toList_scanlM [Monad m] [LawfulMonad m] {f : β → α → m β} {as : Array α} :
    toList <$> as.scanlM f init = as.toList.scanlM f init := by
  simp [← toArray_scanlM_toList]

theorem scanrM.loop_toList [Monad m] [LawfulMonad m] {f : α → β → m β}
    {start : Nat} {h : start ≤ as.size} :
    scanrM.loop f init as start stop h acc =
      return (← as.toList.drop stop
                  |>.take (start - stop)
                  |>.scanrM f init)
                ++ acc.toList.reverse
                |>.toArray := by
  induction h_ind : start - stop generalizing stop acc init start with
  | zero =>
    grind [scanrM.loop, append_eq_toArray_iff, toList_reverse]
  | succ n ih =>
    unfold scanrM.loop
    simp_all only [bind_pure_comp, show stop < start by omega, ↓reduceDIte]
    conv =>
      lhs
      arg 2
      ext a
      rw [ih (start := start - 1) (stop := stop) (acc := acc.push init) (by omega)]
    have h_list : List.take (n + 1) (List.drop stop as.toList)
      = as[stop] :: List.take n (List.drop (stop + 1) as.toList) := by
        rw [List.drop_eq_getElem_cons (by simp; omega)]
        simp only [getElem_toList, List.take_succ_cons]
    have h_rev_list : (List.take (n + 1) (List.drop stop as.toList)).reverse
      = as[start - 1] :: (List.take n (List.drop stop as.toList)).reverse := by
        have h_eq : start - 1 = stop + n := by omega
        rw [← List.take_append_getElem (by simp; omega : n < (List.drop stop as.toList).length)]
        simp [List.reverse_append, List.getElem_drop, h_eq]
    simp_all only [Array.toList_push, List.reverse_append, List.reverse_cons,
      Functor.map_map , List.scanrM_eq_scanlM_reverse]
    simp_all [flip]

theorem toArray_scanrM_toList [Monad m] [LawfulMonad m] {f : α → β → m β} {as : Array α} :
    List.toArray <$> as.toList.scanrM f init = as.scanrM f init := by
  simp [scanrM, Array.scanrM.loop_toList, ← Array.length_toList]

@[simp, grind =]
theorem toList_scanrM [Monad m] [LawfulMonad m] {f : α → β → m β} {as : Array α} :
    toList <$> as.scanrM f init = as.toList.scanrM f init := by
  simp [← toArray_scanrM_toList]

theorem extract_scanlM [Monad m] [LawfulMonad m] {f : β → α → m β} {as : Array α} :
    (as.extract start stop).scanlM f init  = as.scanlM f init start stop := by
  rw (occs := [2]) [scanlM]
  rw [scanlM.loop_toList, ← toArray_scanlM_toList, bind_pure_comp]
  simp_all only [toList_extract, List.nil_append]
  skip
  grind [List.take_eq_take_iff, List.drop_eq_drop_iff]

theorem extract_scanrM [Monad m] [LawfulMonad m] {f : α → β → m β} {as : Array α} :
    (as.extract stop start).scanrM f init = as.scanrM f init start stop := by
  rw (occs := [2]) [scanrM]
  rw [scanrM.loop_toList, ← toArray_scanrM_toList, bind_pure_comp]
  simp_all only [toList_extract]
  grind [List.take_eq_take_iff, List.drop_eq_drop_iff]

@[simp, grind =]
theorem scanlM_empty [Monad m] {f : β → α → m β} {start stop : Nat} :
    #[].scanlM f init start stop = pure #[init] := by
  simp [scanlM, scanlM.loop]

@[grind =]
theorem scanrM_empty [Monad m] {f : α → β → m β} {start stop : Nat} :
    #[].scanrM f init start stop = pure #[init] := by
  simp [scanrM, scanrM.loop]

theorem scanlM_reverse [Monad m] [LawfulMonad m] {f : β → α → m β} {as : Array α} :
    as.reverse.scanlM f init = Array.reverse <$> (as.scanrM (flip f) init) := by
  simp only [← toArray_scanlM_toList, ← toArray_scanrM_toList, toList_reverse,
    List.scanlM_reverse, Functor.map_map, List.reverse_toArray]

@[simp]
theorem scanlM_pure [Monad m] [LawfulMonad m] {f : β → α → β} {as : Array α} :
    as.scanlM (m := m) (pure <| f · ·) init = pure (as.scanl f init) := by
  simp only [scanl, ← toArray_scanlM_toList, ← toArray_scanlM_toList,
    List.scanlM_pure, map_pure, pure,Id.run_map]
  rfl

@[simp]
theorem scanrM_pure [Monad m] [LawfulMonad m] {f : α → β → β} {as : Array α} :
    as.scanrM (m := m) (pure <| f · ·) init = pure (as.scanr f init) := by
  simp only [scanr, ← toArray_scanrM_toList, ← toArray_scanrM_toList,
    List.scanrM_pure, map_pure, pure, Id.run_map]
  rfl

theorem idRun_scanlM {f : β → α → Id β} {as : Array α} :
    (as.scanlM f init).run = as.scanl (f · · |>.run) init :=
  scanlM_pure

theorem idRun_scanrM {f : α → β → Id β} {as : Array α} :
    (as.scanrM f init).run = as.scanr (f · · |>.run) init :=
  scanrM_pure

@[grind =]
theorem scanlM_map [Monad m] [LawfulMonad m] {f : α₁ → α₂ } {g: β → α₂ → m β} {as : Array α₁} :
    (as.map f).scanlM g init = as.scanlM (g · <| f ·) init := by
  simp only [← toArray_scanlM_toList, toList_map, List.scanlM_map]

@[grind =]
theorem scanrM_map [Monad m] [LawfulMonad m] {f : α₁ → α₂ } {g: α₂ → β → m β} {as : Array α₁} :
    (as.map f).scanrM g init = as.scanrM (fun a b => g (f a) b) init := by
  simp only [← toArray_scanrM_toList, toList_map, List.scanrM_map]

/-- ### Array.scanl -/

theorem scanl_eq_scanlM {f : β → α → β} {as: Array α} :
    as.scanl f init = (as.scanlM (m := Id) (pure <| f · ·) init).run := by
  simp

theorem scanl_toList {f: β → α → β} {as : Array α} :
    (as.toList.scanl f init).toArray = as.scanl f init := by
  simp only [scanl_eq_scanlM, ← toArray_scanlM_toList, List.scanl, pure, Id.run_map]

@[simp, grind =]
theorem toList_scanl {f : β → α → β} {as: Array α} :
    (as.scanl f init).toList = as.toList.scanl f init := by
  rw [← scanl_toList]

@[simp]
theorem size_scanl {f : β → α → β} (init : β) (as : Array α) :
    size (scanl f init as) = as.size + 1 := by
  grind [size_eq_length_toList]

grind_pattern size_scanl => scanl f init as

@[grind =]
theorem scanl_empty {f : β → α → β} (init : β) :
    scanl f init #[] = #[init] := by
  apply toList_inj.mp
  grind

@[grind =]
theorem scanl_singleton {f : β → α → β} :
    scanl f init #[a] = #[init, f init a] := by
  apply toList_inj.mp
  grind

@[simp]
theorem scanl_ne_empty {f : β → α → β} : scanl f init as ≠ #[] := by grind

-- This pattern can be removed after moving to a lean version containing
-- https://github.com/leanprover/lean4/pull/11760
local grind_pattern Array.eq_empty_of_size_eq_zero => xs.size where
  guard xs.size = 0

@[simp]
theorem scanl_iff_empty {f : β → α → β} (c : β) :
    scanl f init as = #[c] ↔ c = init ∧ as = #[] := by
  grind

@[simp, grind =]
theorem getElem_scanl {f : β → α → β} {as: Array α} (h : i < (as.scanl f init).size) :
    (as.scanl f init)[i]'h = foldl f init (as.take i) := by
  simp only [←foldl_toList, ←scanl_toList, List.getElem_toArray, List.getElem_scanl,
    take_eq_extract, toList_extract, List.extract_eq_drop_take, Nat.sub_zero, List.drop_zero]

@[grind =]
theorem getElem?_scanl {f : β → α → β} :
    (scanl f a l)[i]? = if i ≤ l.size then some (foldl f a (l.take i)) else none := by
  grind

@[grind _=_]
theorem take_scanl {f : β → α → β} (init : β) (as : Array α) :
    (scanl f init as).take (i + 1) = scanl f init (as.take i) := by
  grind

theorem getElem?_scanl_zero {f : β → α → β} : (scanl f init as)[0]? = some init := by simp

theorem getElem_scanl_zero {f : β → α → β} : (scanl f init as)[0] = init := by simp

theorem getElem?_succ_scanl {f : β → α → β} :
    (scanl f init as)[i + 1]? = (scanl f init as)[i]?.bind fun x => as[i]?.map fun y => f x y := by
  simp [← scanl_toList, List.getElem?_succ_scanl]

theorem getElem_succ_scanl {f : β → α → β} (h : i + 1 < (scanl f b as).size) :
    (as.scanl f b)[i + 1] = f (as.scanl f b)[i] (as[i]'(by grind)) := by
  simp only [← scanl_toList, List.getElem_toArray, List.getElem_succ_scanl, List.getElem_scanl,
    getElem_toList]

@[grind =]
theorem scanl_push {f : β → α → β} {init: β} {a : α} {as : Array α} :
    (as.push a).scanl f init = (as.scanl f init).push (f (as.foldl f init) a) := by
  simp only [← scanl_toList, toList_push, List.scanl_append, foldl_toList, List.scanl_cons,
    List.scanl_nil, List.tail_cons, List.push_toArray]

@[grind =]
theorem scanl_map {f : γ → β → γ} {g : α → β} (init : γ) (as : Array α) :
    scanl f init (as.map g) = scanl (f · <| g ·) init as := by
  simp only [← scanl_toList, toList_map, List.scanl_map]

@[simp, grind =]
theorem back_scanl {f : β → α → β} {as : Array α} :
    (as.scanl f init).back = as.foldl f init := by
  simp [Array.back_eq_getElem]

theorem back_scanl? {f : β → α → β} {as : Array α} :
    (as.scanl f init).back? = some (as.foldl f init) := by
  simp [Array.back?_eq_getElem?]

/-! ### Array.scanr -/

theorem scanr_eq_scanrM {f : α → β → β} {as : Array α} :
    as.scanr f init = (as.scanrM (m := Id) (pure <| f · ·) init).run := by
  simp

theorem scanr_toList {f : α → β → β} {as : Array α} :
    (as.toList.scanr f init).toArray = as.scanr f init := by
  simp only [scanr_eq_scanrM, ← toArray_scanrM_toList, List.scanr, pure, Id.run_map]

@[simp, grind =]
theorem toList_scanr {f : α → β → β} {as : Array α} :
    (as.scanr f init).toList = as.toList.scanr f init := by
  rw [← scanr_toList]

@[simp]
theorem size_scanr {f : α → β → β} (init : β) (as : Array α) :
    size (as.scanr f init) = as.size + 1 := by
  grind [size_eq_length_toList]

grind_pattern size_scanr => scanr f init as

@[grind =]
theorem scanr_empty {f : α → β → β} {init: β} :
    #[].scanr f init = #[init] := by
  apply toList_inj.mp
  grind

@[simp]
theorem scanr_ne_empty {f : α → β → β} {as : Array α} :
    as.scanr f init ≠ #[] := by
  grind

@[grind =]
theorem scanr_push {f : α → β → β} {as : Array α} :
    (as.push a).scanr f init = (as.scanr f (f a init)).push init := by
  apply toList_inj.mp
  grind

@[simp, grind =]
theorem back_scanr {f : α → β → β} {as : Array α} : (as.scanr f init).back = init := by
  simp [←getLast_toList, List.getLast_scanr]

theorem back?_scanr {f : α → β → β} {as : Array α} :
    (as.scanr f init).back? = some init := by
  simp [←getLast?_toList, List.getLast?_scanr]

@[simp, grind =]
theorem getElem_scanr {f : α → β → β} (h : i < (scanr f b l).size) :
    (scanr f b l)[i] = foldr f b (l.drop i) := by
  simp only [← foldr_toList, ← scanr_toList, ←getElem_toList, List.getElem_scanr, toList_drop]

@[grind =]
theorem getElem?_scanr {f : α → β → β} :
    (scanr f b as)[i]? = if i < as.size + 1 then some (foldr f b (as.drop i)) else none := by
  simp only [← foldr_toList, ← scanr_toList, List.getElem?_toArray, toList_drop]
  simp only [← length_toList, List.getElem?_scanr]

theorem getElem_scanr_zero {f : α → β → β} :
    (scanr f init as)[0] = as.foldr f init := by
  simp

theorem getElem?_scanr_zero {f : α → β → β} :
    (scanr f init as)[0]? = some (as.foldr f init ) := by
  simp

@[grind =]
theorem scanr_map {f : β → γ → γ} {g : α → β} (init : γ) (as : Array α) :
    scanr f init (as.map g) = scanr (fun x acc => f (g x) acc) init as := by
  simp only [← scanr_toList, toList_map, List.scanr_map]

@[grind =]
theorem scanl_reverse {f : β → α → β} {as : Array α} :
    scanl f init as.reverse = reverse (scanr (flip f) init as) := by
  apply toList_inj.mp
  simp only [← scanl_toList, ← scanr_toList, toList_reverse, List.scanl_reverse,
    List.reverse_toArray]

 end Array

namespace Subarray
theorem scanlM_eq_scanlM_extract [Monad m] [LawfulMonad m] {f : β → α → m β} {as : Subarray α} :
    as.scanlM f init = (as.array.extract as.start as.stop).scanlM f init := by
  unfold scanlM
  simp only [Array.extract_scanlM]

theorem scanrM_eq_scanrM_extract [Monad m] [LawfulMonad m] {f : α → β → m β} {as : Subarray α} :
    as.scanrM f init = (as.array.extract as.stop as.start).scanrM f init := by
  unfold scanrM
  simp only [Array.extract_scanrM]
end Subarray
