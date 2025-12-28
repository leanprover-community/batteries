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

private theorem scanlM_loop_eq_list_scanlM [Monad m] [LawfulMonad m] 
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
          
theorem scanlM_toList [Monad m] [LawfulMonad m] 
    {f : β → α → m β} {init : β} {as : Array α} :
    (return (← as.toList.scanlM f init).toArray) = as.scanlM f init := by
  unfold scanlM
  simp [Array.scanlM_loop_eq_list_scanlM, ←Array.length_toList]


-- TODO: come back and simplify this proof? And/or simplify the structure of Arrat.scacnrM to make it more amenable
private theorem scanrM_loop_toList [Monad m] [LawfulMonad m] 
    {f : α → β → m β} {as : Array α} {init : β} 
    {start stop : Nat} {h : start ≤ as.size}
    {acc : Array β} 
    : (return (←scanrM.loop f init as start stop h acc).toList)
      = return (← as.toList.drop stop
                  |>.take (start - stop) 
                  |>.scanrM f init)
                ++ acc.toList.reverse
    := by 
      induction h_ind : start - stop generalizing stop acc init start with
        | zero =>
          unfold scanrM.loop
          simp [show ¬(stop < start) by omega]
        | succ n ih => 
          unfold scanrM.loop
          simp_all only [bind_pure_comp, show stop < start by omega, ↓reduceDIte, map_bind]
          conv => lhs; arg 2; ext a; rw [ih (start := start - 1) (stop := stop) (acc := acc.push init) (by omega)]
          have h_list : List.take (n + 1) (List.drop stop as.toList) = as[stop] :: List.take n (List.drop (stop + 1) as.toList) := by
            rw [List.drop_eq_getElem_cons (by simp; omega)]
            simp 
          have h_rev_list : (List.take (n + 1) (List.drop stop as.toList)).reverse = as[start - 1] :: (List.take n (List.drop stop as.toList)).reverse 
            := by
            have h_eq : start - 1 = stop + n := by omega
            rw [← List.take_append_getElem (by simp; omega : n < (List.drop stop as.toList).length)]
            simp [List.reverse_append, List.getElem_drop, h_eq]
          simp_all only [ Array.toList_push , List.reverse_append , List.reverse_cons
                        , List.reverse_nil , List.nil_append , Functor.map_map 
                        , List.scanrM 
                        ]
          simp_all [flip]


theorem scanrM_toList [Monad m] [LawfulMonad m] 
    {f : α → β → m β} {init : β} {as : Array α} :
    (return (← as.toList.scanrM f init).toArray) = as.scanrM f init := by
  simp only [scanrM, bind_pure_comp]
  have h := scanrM_loop_toList (f := f) (as := as) (init := init) 
            (start := as.size) (stop := 0) (h := Nat.le_refl _) (acc := #[])
  have h' := congrArg (Functor.map List.toArray) h
  simp only [bind_pure_comp, Nat.sub_zero, List.drop_zero, List.reverse_nil, List.append_nil,
    bind_pure, Nat.le_refl, Nat.min_eq_left, Nat.zero_le] at ⊢ h
  simp_all [← Array.length_toList, List.take_length]


theorem scanlM_nil [Monad m] {f : β → α → m β} {init : β} 
  : #[].scanlM f init = pure #[init] := by simp [scanlM, scanlM.loop]

theorem scanrM_nil [Monad m] {f : α → β → m β} {init : β} 
  : #[].scanrM f init = pure #[init] := by simp [scanrM, scanrM.loop]

 end Array
