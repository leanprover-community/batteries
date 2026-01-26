/-
Copyright (c) 2025 Chad Sharp. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chad Sharp
-/

module
public import Batteries.Data.Iterators.Scan
public import Batteries.Data.List.Scan
public import Batteries.Data.Array.Scan

namespace Std
open Std.Iterators Std.Iterators.Types

theorem IterM.mk_def {state : ScanM α m n β γ f} :
    (IterM.mk state n γ : IterM n γ) = { internalState := state } := rfl

theorem toList_scanM_emittedTrue [Iterator α Id β] [Finite α Id] [Monad m] [LawfulMonad m]
  {f : γ → β → m γ} {acc : γ} {it : IterM (α := α) Id β} :
    (IterM.mk (m := m) (β := γ) (ScanM.mk (m := Id) (f := f) it.internalState acc true)).toList
      = (return (← List.scanlM f acc (← it.toList)).tail) := by
  induction it using IterM.inductSteps generalizing acc
  rename_i it ihy ihs
  rw [IterM.toList_eq_match_step, IterM.toList_eq_match_step]
  simp only [Iterator.step, liftM, monadLift, Id.run, bind_pure_comp, pure_bind,
    IterM.mk_def, IterM.step, Bool.true_eq_false, ↓reduceDIte, bind, pure] at ⊢ ihy ihs
  match hstep : it.step.inflate with
  | ⟨.yield inner' out, hp⟩ =>
    simp only [bind_map_left, Shrink.inflate_deflate, List.scanlM_cons, bind_pure_comp, map_bind]
    skip
    apply bind_congr
    intro a
    rw [ihy hp, ← List.scanlM_cons_head_tail]
    simp
  | ⟨.skip inner', hp⟩ =>
    simp_all
  | ⟨.done, hp⟩ =>
    simp_all

public section

@[simp]
theorem IterM.toList_scanM [Iterator α Id β] [Finite α Id] [Monad m] [LawfulMonad m]
    {f : γ → β → m γ} {init : γ} (it : IterM (α := α) Id β) :
    (it.scanM f init).toList = List.scanlM f init it.toList := by
  simp only [IterM.scanM]
  rw [IterM.toList_eq_match_step]
  simp only [Iterator.step, IterM.step, ← mk_def, bind_pure_comp]
  have := List.scanlM_cons_head_tail (as := it.toList) (init := init) (f := f)
  simp_all [liftM, monadLift, Id.run, toList_scanM_emittedTrue]

@[simp]
theorem Iter.toList_scanM [Iterator α Id β] [Finite α Id] [Monad m] [LawfulMonad m]
    {f : γ → β → m γ} {init : γ} (it : Iter (α := α) β) :
    (it.scanM f init).toList = List.scanlM f init it.toList := by
  unfold Iter.scanM
  apply IterM.toList_scanM

@[simp]
theorem IterM.toList_scan [Iterator α Id β] [Finite α Id]
    {f : γ → β → γ} {init : γ} (it : IterM (α := α) Id β) :
    (it.scan f init).toList = List.scanl f init it.toList := by
  simp [List.scanl, scan, pure, Id.run]

@[simp]
theorem Iter.toList_scan [Iterator α Id β] [Finite α Id]
    {f : γ → β → γ} {init : γ} (it : Iter (α := α) β) :
    (it.scan f init).toList = List.scanl f init it.toList := by
  simp [Iter.scan, List.scanl]

@[simp]
theorem IterM.toArray_scanM [Iterator α Id β] [Finite α Id] [Monad m] [LawfulMonad m]
    {f : γ → β → m γ} {init : γ} (it : IterM (α := α) Id β) :
    (it.scanM f init).toArray = Array.scanlM f init it.toArray := by
  repeat rw [← toArray_toList]
  rw [IterM.toList_scanM, ← Array.scanlM_toList]
  congr

@[simp]
theorem Iter.toArray_scanM [Iterator α Id β] [Finite α Id] [Monad m] [LawfulMonad m]
    {f : γ → β → m γ} {init : γ} (it : Iter (α := α) β) :
    (it.scanM f init).toArray = Array.scanlM f init it.toArray := by
  unfold Iter.scanM
  apply IterM.toArray_scanM

@[simp]
theorem IterM.toArray_scan [Iterator α Id β] [Finite α Id]
    {f : γ → β → γ} {init : γ} (it : IterM (α := α) Id β) :
    (it.scan f init).toArray = Array.scanl f init it.toArray := by
  simp [Array.scanl_eq_scanlM, scan, pure, Id.run]

@[simp]
theorem Iter.toArray_scan [Iterator α Id β] [Finite α Id]
    {f : γ → β → γ} {init : γ} (it : Iter (α := α) β) :
    (it.scan f init).toArray = Array.scanl f init it.toArray := by
  unfold scan
  apply IterM.toArray_scan

end
end Std
