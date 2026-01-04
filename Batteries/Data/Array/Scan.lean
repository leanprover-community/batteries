/-
Copyright (c) 2014 Parikshit Khanna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chad Sharp
-/
module

public import Batteries.Data.Array.Basic
public import Batteries.Data.Array.Lemmas
import Batteries.Data.List.Scan

@[expose] public section

/-!
# Array

Prove basic results about `Array.scanl`, `Array.scanr`, `Array.scanlM` and `Array.scanrM`.
-/


namespace Array

theorem scanlM_loop_toList [Monad m] [LawfulMonad m]
    {f : β → α → m β} {as : Array α}
    {start stop : Nat} {h : stop ≤ as.size}
    {acc : Array β} {init : β}
    : scanlM.loop f init as start stop h acc
      = return acc.toList
               ++ (← as.toList.drop start
                  |>.take (stop - start)
                  |>.scanlM f init)
               |>.toArray
    := by
      induction h_ind : stop - start generalizing start acc init with
        | zero =>
          unfold scanlM.loop
          simp [show ¬(start < stop) by omega, ← Array.toList_push]
        | succ n ih =>
          unfold scanlM.loop
          rw [List.drop_eq_getElem_cons (by simp; omega)]
          simp [ show start < stop by omega
               , show stop - (start + 1) = n by omega
               , ih
               ]

theorem scanlM_toList [Monad m] [LawfulMonad m] {f : β → α → m β} {init : β} {as : Array α}
  : List.toArray <$> as.toList.scanlM f init = as.scanlM f init
  := by
    unfold scanlM
    simp [Array.scanlM_loop_toList, ←Array.length_toList]


@[simp, grind =]
theorem toList_scanlM [Monad m] [LawfulMonad m] {f : β → α → m β} {init : β} {as : Array α}
  : toList <$> as.scanlM f init = as.toList.scanlM f init
  := by
    rw [← scanlM_toList]
    simp


-- TODO: come back and simplify this proof? And/or simplify the structure of Arrat.scacnrM to make
-- it more amenable
theorem scanrM_loop_toList [Monad m] [LawfulMonad m]
    {f : α → β → m β} {as : Array α} {init : β}
    {start stop : Nat} {h : start ≤ as.size}
    {acc : Array β}
    : scanrM.loop f init as start stop h acc
      = return (← as.toList.drop stop
                  |>.take (start - stop)
                  |>.scanrM f init)
                ++ acc.toList.reverse
                |>.toArray
    := by
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
            = as[stop] :: List.take n (List.drop (stop + 1) as.toList)
            := by
              rw [List.drop_eq_getElem_cons (by simp; omega)]
              simp

          have h_rev_list : (List.take (n + 1) (List.drop stop as.toList)).reverse
            = as[start - 1] :: (List.take n (List.drop stop as.toList)).reverse
            := by
              have h_eq : start - 1 = stop + n := by omega
              rw [← List.take_append_getElem
                (by simp; omega : n < (List.drop stop as.toList).length)]
              simp [List.reverse_append, List.getElem_drop, h_eq]

          simp_all only [ Array.toList_push , List.reverse_append , List.reverse_cons
                         , Functor.map_map
                        , List.scanrM
                        ]
          simp_all [flip]


theorem scanrM_toList [Monad m] [LawfulMonad m] {f : α → β → m β} {init : β} {as : Array α}
  : List.toArray <$> as.toList.scanrM f init = as.scanrM f init
  := by
    unfold scanrM
    simp [Array.scanrM_loop_toList, ← Array.length_toList]


@[simp, grind =]
theorem toList_scanrM [Monad m] [LawfulMonad m]
  {f : α → β → m β} {init : β} {as : Array α}
  : toList <$> as.scanrM f init = as.toList.scanrM f init
  := by
    rw [← scanrM_toList]
    simp

-- TODO: rewrite without requiring LawfulMonad?
-- In principle it probably shouldn't require it its just that scanlM_loop_toList does
theorem scanlM_extract [Monad m] [LawfulMonad m]
    {f : β → α → m β} {init : β} {as : Array α} {start stop : Nat}
  : as.scanlM f init start stop = (as.extract start stop).scanlM f init
  := by
    rw (occs := [1]) [scanlM]
    rw [scanlM_loop_toList, ← scanlM_toList, bind_pure_comp]
    simp_all [← length_toList]
    grind [List.take_eq_take_iff, List.drop_eq_drop_iff]


-- TODO: rewrite without requiring LawfulMonad?
-- In principle it probably shouldn't require it its just that scanlM_loop_toList does
theorem scanrM_extract [Monad m] [LawfulMonad m]
    {f : α → β → m β} {init : β} {as : Array α} {start stop : Nat}
  : as.scanrM f init start stop = (as.extract stop start).scanrM f init
  := by
    rw (occs := [1]) [scanrM]
    rw [scanrM_loop_toList, ← scanrM_toList, bind_pure_comp]
    grind [List.take_eq_take_iff, toList_extract]

@[simp, grind=]
theorem scanlM_empty [Monad m] {f : β → α → m β} {init : β}
  : #[].scanlM f init = pure #[init] := by simp [scanlM, scanlM.loop]

@[simp, grind=]
theorem scanrM_empty [Monad m] {f : α → β → m β} {init : β}
  : #[].scanrM f init = pure #[init] := by simp [scanrM, scanrM.loop]

@[simp]
theorem scanlM_reverse [Monad m] [LawfulMonad m] {f : β → α → m β} {init : β} {as : Array α}
  : as.reverse.scanlM f init = Array.reverse <$> (as.scanrM (flip f) init)
  := by
    rw [← scanlM_toList, ← scanrM_toList]
    simp

@[simp]
theorem scanlM_pure [Monad m] [LawfulMonad m] {f : β → α → β} {init : β} {as : Array α}
  : as.scanlM (m := m) (pure <| f · ·) init = pure (as.scanl f init)
  := by
    unfold scanl
    rw [← scanlM_toList, ← scanlM_toList, List.scanlM_pure]
    simp only [map_pure, Id.run_map]
    rfl

@[simp]
theorem scanrM_pure [Monad m] [LawfulMonad m] {f : α → β → β} {init : β} {as : Array α}
  : as.scanrM (m := m) (pure <| f · ·) init = pure (as.scanr f init)
  := by
    unfold scanr
    rw [← scanrM_toList, ← scanrM_toList, List.scanrM_pure]
    simp only [map_pure, Id.run_map]
    rfl

theorem idRun_scanlM {f : β → α → Id β} {init : β} {as : Array α}
  : (as.scanlM f init).run = as.scanl (f · · |>.run) init
  := scanlM_pure

theorem idRun_scanrM {f : α → β → Id β} {init : β} {as : Array α }
  : (as.scanrM f init).run = as.scanr (f · · |>.run) init
  := scanrM_pure

@[simp, grind =]
theorem scanlM_map [Monad m] [LawfulMonad m] {f : α₁ → α₂ } {g: β → α₂ → m β} {as : Array α₁} {init : β}
  : (as.map f).scanlM g init = as.scanlM (g · <| f ·) init
  := by
    repeat rw [← scanlM_toList]
    simp

@[simp, grind =]
theorem scanrM_map [Monad m] [LawfulMonad m] {f : α₁ → α₂ } {g: α₂ → β → m β} {as : Array α₁} {init : β}
  : (as.map f).scanrM g init = as.scanrM (fun a b => g (f a) b) init
  := by
    repeat rw [← scanrM_toList]
    simp


/-- ### Array.scanl -/

theorem scanl_eq_scanlM {f : β → α → β} {init : β} {as: Array α}
  : as.scanl f init = (as.scanlM (m := Id) (pure <| f · ·) init).run
  := by simp

theorem scanl_toList {f: β → α → β} {init : β} {as : Array α}
  : (as.toList.scanl f init).toArray = as.scanl f init
  := by
    rw [scanl_eq_scanlM, ← scanlM_toList]
    simp [Id.run_map, pure, List.scanl]


@[simp, grind =]
theorem toList_scanl {f : β → α → β} {init : β} {as: Array α}
  : (as.scanl f init).toList = as.toList.scanl f init
  := by rw [← scanl_toList]

@[simp]
theorem size_scanl {f : β → α → β} (init : β) (as : Array α)
  : size (scanl f init as) = as.size + 1
  := by grind [size_eq_length_toList]

grind_pattern size_scanl => scanl f init as

@[simp, grind =]
theorem scanl_empty {f : β → α → β} (init : β)
  : scanl f init #[] = #[init]
  := by
    apply toList_inj.mp
    grind

@[simp, grind =]
theorem scanl_singleton {f : β → α → β}
  : scanl f init #[a] = #[init, f init a]
  := by
    apply toList_inj.mp
    grind

@[simp]
theorem scanl_ne_empty {f : β → α → β}
  : scanl f init as ≠ #[]
  := by grind

-- This pattern can be removed after moving to a lean version containing
-- https://github.com/leanprover/lean4/pull/11760
local grind_pattern Array.eq_empty_of_size_eq_zero => xs.size where
  guard xs.size = 0

@[simp]
theorem scanl_iff_empty {f : β → α → β} (c : β)
  : scanl f init as = #[c] ↔ c = init ∧ as = #[]
  := by grind

@[simp, grind =]
theorem getElem_scanl {f : β → α → β} {as: Array α} {init : β} (h : i < (as.scanl f init).size)
  : (as.scanl f init)[i]'h = foldl f init (as.take i)
  := by
    simp only [←foldl_toList, ←scanl_toList]
    simp

@[grind =]
theorem getElem?_scanl {f : β → α → β} :
    (scanl f a l)[i]? = if i ≤ l.size then some (foldl f a (l.take i)) else none := by
  grind


@[grind _=_]
theorem take_scanl {f : β → α → β} (init : β) (as : Array α) (i : Nat)
  : (scanl f init as).take (i + 1) = scanl f init (as.take i)
  := by grind

theorem getElem?_scanl_zero {f : β → α → β} : (scanl f init as)[0]? = some init := by
  simp

theorem getElem_scanl_zero {f : β → α → β} : (scanl f init as)[0] = init := by
  simp

theorem getElem?_succ_scanl {f : β → α → β}
  : (scanl f init as)[i + 1]? = (scanl f init as)[i]?.bind fun x => as[i]?.map fun y => f x y
  := by
    simp [← scanl_toList, List.getElem?_succ_scanl]

theorem getElem_succ_scanl {f : β → α → β} (h : i + 1 < (scanl f b as).size)
  : (as.scanl f b)[i + 1] = f (as.scanl f b)[i] (as[i]'(by grind))
  := by
    simp only [← scanl_toList, List.getElem_toArray, List.getElem_succ_scanl]
    simp

@[simp, grind =]
theorem scanl_push {f : β → α → β} {init: β} {a : α} {as : Array α}
  : (as.push a).scanl f init = (as.scanl f init).push (f (as.foldl f init) a)
  := by
    repeat rw [← scanl_toList]
    simp [List.scanl_append]

@[grind =]
theorem scanl_map {f : γ → β → γ} {g : α → β} (init : γ) (as : Array α)
  : scanl f init (as.map g) = scanl (f · <| g ·) init as
  := by
    repeat rw [← scanl_toList]
    simp [List.scanl_map]

@[simp, grind=]
theorem back_scanl {f : β → α → β} {init : β} {as : Array α}
  : (as.scanl f init).back = as.foldl f init
  := by simp [Array.back_eq_getElem]

theorem back_scanl? {f : β → α → β} {init : β} {as : Array α}
  : (as.scanl f init).back? = some (as.foldl f init)
  := by simp [Array.back?_eq_getElem?]


/-! ### Array.scanr -/

theorem scanr_eq_scanrM {f : α → β → β} {init : β} {as : Array α}
  : as.scanr f init = (as.scanrM (m := Id) (pure <| f · ·) init).run
  := by simp

theorem scanr_toList {f : α → β → β} {init : β} {as : Array α}
  : (as.toList.scanr f init).toArray = as.scanr f init
  := by
    rw [scanr_eq_scanrM, ← scanrM_toList]
    simp [Id.run_map, pure, List.scanr]

@[simp, grind =]
theorem toList_scanr {f : α → β → β} {init : β} {as : Array α}
  : (as.scanr f init).toList = as.toList.scanr f init
  := by rw [← scanr_toList]

@[simp]
theorem size_scanr {f : α → β → β} (init : β) (as : Array α)
  : size (as.scanr f init) = as.size + 1
  := by grind [size_eq_length_toList]

grind_pattern size_scanr => scanr f init as

@[simp, grind =]
theorem scanr_empty {f : α → β → β} {init: β}
  : #[].scanr f init = #[init]
  := by
    apply toList_inj.mp
    grind

@[simp]
theorem scanr_ne_empty {f : α → β → β} {init : β} {as : Array α}
  : as.scanr f init ≠ #[]
  := by grind

@[simp, grind =]
theorem scanr_push {f : α → β → β} {init : β} {a : α} {as : Array α}
  : (as.push a).scanr f init = (as.scanr f (f a init)).push init
  := by
    apply toList_inj.mp
    grind

@[simp, grind=]
theorem back_scanr {f : α → β → β} {init: β} {as : Array α}
  : (as.scanr f init).back = init
  := by simp [←getLast_toList, List.getLast_scanr]

theorem back?_scanr {f : α → β → β} {init : β} {as : Array α}
  : (as.scanr f init).back? = some init
  := by simp [←getLast?_toList, List.getLast?_scanr]

@[simp, grind=]
theorem getElem_scanr {f : α → β → β} (h : i < (scanr f b l).size)
  : (scanr f b l)[i] = foldr f b (l.drop i)
  := by simp only [← foldr_toList, ← scanr_toList, ←getElem_toList, List.getElem_scanr, toList_drop]

@[grind =]
theorem getElem?_scanr {f : α → β → β}
  : (scanr f b as)[i]? = if i < as.size + 1 then some (foldr f b (as.drop i)) else none
  := by
    simp only [← foldr_toList, ← scanr_toList, List.getElem?_toArray, toList_drop]
    simp only [← length_toList, List.getElem?_scanr]

@[simp, grind=]
theorem getElem_scanr_zero {f : α → β → β}
  : (scanr f init as)[0] = as.foldr f init
  := by simp

@[simp, grind=]
theorem getElem?_scanr_zero {f : α → β → β}
  : (scanr f init as)[0]? = some (as.foldr f init )
  := by simp

@[grind =]
theorem scanr_map {f : β → γ → γ} {g : α → β} (init : γ) (as : Array α)
  : scanr f init (as.map g) = scanr (fun x acc => f (g x) acc) init as
  := by
    repeat rw [← scanr_toList]
    simp [List.scanr_map]

@[simp, grind =]
theorem scanl_reverse {f : β → α → β} {init : β} {as : Array α}
  : scanl f init as.reverse = reverse (scanr (flip f) init as)
  := by
    apply toList_inj.mp
    simp only [← scanl_toList, ← scanr_toList]
    simp

 end Array

namespace Subarray
theorem scanlM_extract [Monad m] [LawfulMonad m] {f : β → α → m β} {init : β} {as : Subarray α}
  : as.scanlM f init = (as.array.extract as.start as.stop).scanlM f init
  := by
    unfold scanlM
    apply Array.scanlM_extract

theorem scanrM_extract [Monad m] [LawfulMonad m] {f : α → β → m β} {init : β} {as : Subarray α}
  : as.scanrM f init = (as.array.extract as.stop as.start).scanrM f init
  := by
    unfold scanrM
    apply Array.scanrM_extract
end Subarray

