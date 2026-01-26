/-
Copyright (c) 2025 Chad Sharp. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chad Sharp
-/

module
public import Batteries.Data.Iterators.Scan
public import Batteries.Data.List.Scan
public import Batteries.Data.Array.Scan

public section

namespace Std.Iterators

private theorem toIterM_eq_mk {state : ScanM α m n β γ f} :
    (toIterM state n γ : IterM n γ) = { internalState := state } := rfl

private theorem toList_scanM_emittedTrue [Iterator α Id β] [Finite α Id] [Monad m] [LawfulMonad m]
  [IteratorCollect α Id Id (β := β)] [LawfulIteratorCollect α Id Id (β := β)]
  {f : γ → β → m γ} {acc : γ} {it : IterM (α := α) Id β} :
    (toIterM (m := m) (β := γ) (⟨it.internalState, acc, true⟩ : ScanM α Id m β γ f)).toList
      = (return (← List.scanlM f acc (← it.toList)).tail) := by
  induction it using IterM.inductSteps generalizing acc
  rename_i it ihy ihs
  rw [IterM.toList_eq_match_step, IterM.toList_eq_match_step]
  simp only [IterM.step, liftM_bind, ScanM.instIterator, internalState_toIterM]
  simp only [Bool.true_eq_false, ↓reduceDIte, bind_assoc]
  apply bind_congr
  intro step
  match hstep : step.inflate with
  | ⟨.yield inner' out, hp⟩ =>
    simp only [liftM, monadLift, Id.run, pure_bind, toIterM] at ⊢ ihy
    simp only [bind_pure_comp, bind_map_left, Shrink.inflate_deflate,
      List.scanlM_cons, map_bind, Functor.map]
    apply bind_congr
    intro a
    rw [ihy hp, ← List.scanlM_cons_head_tail]
    simp
  | ⟨.skip inner', hp⟩ =>
    simp_all [liftM, monadLift, Id.run, toIterM]
  | ⟨.done, hp⟩ =>
    simp_all

@[simp]
theorem IterM.toList_scanM [Iterator α Id β] [Finite α Id] [Monad m] [LawfulMonad m]
    [IteratorCollect α Id Id (β := β)] [LawfulIteratorCollect α Id Id (β := β)]
    {f : γ → β → m γ} {init : γ} (it : IterM (α := α) Id β) :
    (it.scanM f init).toList = List.scanlM f init it.toList := by
  simp only [IterM.scanM]
  rw [IterM.toList_eq_match_step]
  simp only [Iterator.step, ScanM.instIterator, IterM.step]
  have := List.scanlM_cons_head_tail (as := it.toList) (init := init) (f := f)
  simp_all [← toIterM_eq_mk, liftM, monadLift, Id.run, toList_scanM_emittedTrue]

@[simp]
theorem Iter.toList_scanM [Iterator α Id β] [Finite α Id] [Monad m] [LawfulMonad m]
    [IteratorCollect α Id Id (β := β)] [LawfulIteratorCollect α Id Id (β := β)]
    {f : γ → β → m γ} {init : γ} (it : Iter (α := α) β) :
    (it.scanM f init).toList = List.scanlM f init it.toList := by
  unfold Iter.scanM
  apply IterM.toList_scanM

@[simp]
theorem IterM.toList_scan [Iterator α Id β] [Finite α Id]
    [IteratorCollect α Id Id (β := β)] [LawfulIteratorCollect α Id Id (β := β)]
    {f : γ → β → γ} {init : γ} (it : IterM (α := α) Id β) :
    (it.scan f init).toList = List.scanl f init it.toList := by
  simp [List.scanl, scan, pure, Id.run]

@[simp]
theorem Iter.toList_scan [Iterator α Id β] [Finite α Id]
    [IteratorCollect α Id Id (β := β)] [LawfulIteratorCollect α Id Id (β := β)]
    {f : γ → β → γ} {init : γ} (it : Iter (α := α) β) :
    (it.scan f init).toList = List.scanl f init it.toList := by
  simp [Iter.scan, List.scanl]

@[simp]
theorem IterM.toArray_scanM [Iterator α Id β] [Finite α Id] [Monad m] [LawfulMonad m]
    [IteratorCollect α Id Id (β := β)] [LawfulIteratorCollect α Id Id (β := β)]
    {f : γ → β → m γ} {init : γ} (it : IterM (α := α) Id β) :
    (it.scanM f init).toArray = Array.scanlM f init it.toArray := by
  repeat rw [← toArray_toList]
  rw [IterM.toList_scanM, ← Array.scanlM_toList]
  congr

@[simp]
theorem Iter.toArray_scanM [Iterator α Id β] [Finite α Id] [Monad m] [LawfulMonad m]
    [IteratorCollect α Id Id (β := β)] [LawfulIteratorCollect α Id Id (β := β)]
    {f : γ → β → m γ} {init : γ} (it : Iter (α := α) β) :
    (it.scanM f init).toArray = Array.scanlM f init it.toArray := by
  unfold Iter.scanM
  apply IterM.toArray_scanM

@[simp]
theorem IterM.toArray_scan [Iterator α Id β] [Finite α Id]
    [IteratorCollect α Id Id (β := β)] [LawfulIteratorCollect α Id Id (β := β)]
    {f : γ → β → γ} {init : γ} (it : IterM (α := α) Id β) :
    (it.scan f init).toArray = Array.scanl f init it.toArray := by
  simp [Array.scanl_eq_scanlM, scan, pure, Id.run]

@[simp]
theorem Iter.toArray_scan [Iterator α Id β] [Finite α Id]
    [IteratorCollect α Id Id (β := β)] [LawfulIteratorCollect α Id Id (β := β)]
    {f : γ → β → γ} {init : γ} (it : Iter (α := α) β) :
    (it.scan f init).toArray = Array.scanl f init it.toArray := by
  unfold scan
  apply IterM.toArray_scan

end Std.Iterators
