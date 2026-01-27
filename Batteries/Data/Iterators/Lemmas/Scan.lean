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

namespace Std
open Std.Iterators Std.Iterators.Types

theorem IterM.InternalCombinators.step_scanM {α β γ : Type w} {m : Type w → Type w'}
    {n : Type w → Type w''}
    {f : γ → β → PostconditionT n γ} [Iterator α m β] [MonadLiftT m n] [Monad n]
    {it : IterM (α := α) m β} {acc : γ} {yieldAcc : Bool} :
    (IterM.InternalCombinators.scanM f acc yieldAcc it).step = (do
        if h : yieldAcc = true then
          return .deflate <| .yield
            (IterM.InternalCombinators.scanM f acc false it)
            acc
            (.yieldInit (by simp [IterM.InternalCombinators.scanM, h]))
        else
          match (← it.step).inflate with
          | .yield it' b hp => do
            let ⟨newAcc, h_acc⟩ ← (f acc b).operation
            return .deflate <| .yield
              (IterM.InternalCombinators.scanM f newAcc false it')
              newAcc
              (.yieldNext (by simp [IterM.InternalCombinators.scanM, h]) hp h_acc)
          | .skip it' hp =>
            return .deflate <| .skip
              (IterM.InternalCombinators.scanM f acc false it')
              (.skip (by simp [IterM.InternalCombinators.scanM, h]) hp)
          | .done hp =>
            return .deflate <|
              .done (.done (by simp [IterM.InternalCombinators.scanM, h]) hp)) := by
  cases h: yieldAcc
  case true => rfl
  apply bind_congr
  intro step
  cases step.inflate using PlausibleIterStep.casesOn <;> rfl

private theorem IterM.toList_scanWithPostCondition_afterInit {α β γ : Type w} {m : Type w → Type w'}
    [Monad m] [LawfulMonad m] [Iterator α Id β] [Finite α Id]
    {f : γ → β → PostconditionT m γ} {init : γ} (it : IterM (α := α) Id β) :
    IterM.toList (IterM.InternalCombinators.scanM (m := Id) f init false it) =
      return ((← it.toList.run.scanlM (f · · |>.run) init).tail) := by
  induction it using IterM.inductSteps generalizing init with | step it ihy ihs =>
  rw [IterM.toList_eq_match_step, IterM.toList_eq_match_step]
  simp only [IterM.InternalCombinators.step_scanM, Id.instMonad, ↓reduceDIte, Bool.false_eq_true]
  simp_all only [monadLift, Id.run, bind_pure_comp, liftM]
  match hstep : it.step.inflate with
  | ⟨.yield inner' out, hp⟩ =>
    simp_all only [PostconditionT.run_eq_map, bind_map_left, List.scanlM_cons, pure_bind]
    simp only [Shrink.inflate_deflate, map_bind]
    apply bind_congr
    intro a
    rw [ihy hp, ← List.scanlM_cons_head_tail]
    simp
  | ⟨.skip inner, hp⟩ => simp_all
  | ⟨.done, x⟩ => simp_all

@[simp]
theorem IterM.toList_scanWithPostCondition {α β γ : Type w} {m : Type w → Type w'}
    [Monad m] [LawfulMonad m] [Iterator α Id β] [Finite α Id]
    {f : γ → β → PostconditionT m γ} {init : γ} (it : IterM (α := α) Id β) :
    (it.scanWithPostcondition f init).toList = it.toList.run.scanlM (f · · |>.run) init := by
  unfold IterM.scanWithPostcondition
  rw [IterM.toList_eq_match_step, IterM.InternalCombinators.step_scanM]
  simp only [↓reduceDIte, pure_bind, Shrink.inflate_deflate]
  rw [toList_scanWithPostCondition_afterInit]
  simp only [Id.run, bind_pure_comp]
  rw [← List.scanlM_cons_head_tail]
  simp

@[simp]
theorem IterM.toList_scanM {α β γ : Type w} {m : Type w → Type w'}
    [Monad m] [MonadAttach m] [LawfulMonad m] [WeaklyLawfulMonadAttach m]
    [Iterator α Id β] [Finite α Id]
    {f : γ → β → m γ} {init : γ} (it : IterM (α := α) Id β) :
    (it.scanM f init).toList = it.toList.run.scanlM f init := by
  simp [IterM.scanM, PostconditionT.run_attachLift]

@[simp]
theorem IterM.toList_scan {α β γ : Type w}
    [Iterator α Id β] [Finite α Id]
    {f : γ → β → γ} {init : γ} (it : IterM (α := α) Id β) :
    (it.scan f init).toList = (List.scanl f init it.toList.run : List γ) := by
  simp [IterM.scan, PostconditionT.run_eq_map, List.scanl]
  rfl

@[simp]
theorem Iter.toList_scanWithPostcondition {α β γ : Type w} {m : Type w → Type w'}
    [Monad m] [LawfulMonad m]
    [Iterator α Id β] [Finite α Id]
    {f : γ → β → PostconditionT m γ} {init : γ} (it : Iter (α := α) β) :
    (it.scanWithPostcondition f init).toList = it.toList.scanlM (f · · |>.run) init := by
  simp [Iter.scanWithPostcondition, Iter.toList, Id.run]

@[simp]
theorem Iter.toList_scanM {α β γ : Type w} {m : Type w → Type w'}
    [Monad m] [MonadAttach m] [LawfulMonad m] [WeaklyLawfulMonadAttach m]
    [Iterator α Id β] [Finite α Id]
    {f : γ → β → m γ} {init : γ} (it : Iter (α := α) β) :
    (it.scanM f init).toList = it.toList.scanlM f init := by
  simp [Iter.scanM, Iter.toList, Id.run]

@[simp]
theorem Iter.toList_scan {α β γ : Type w}
    [Iterator α Id β] [Finite α Id]
    {f : γ → β → γ} {init : γ} (it : Iter (α := α) β) :
    (it.scan f init).toList = List.scanl f init it.toList := by
  simp [Iter.scan, IterM.toList_scan]
  rfl

@[simp]
theorem IterM.toArray_scanWithPostCondition {α β γ : Type w} {m : Type w → Type w'}
    [Monad m] [LawfulMonad m] [Iterator α Id β] [Finite α Id]
    {f : γ → β → PostconditionT m γ} {init : γ} (it : IterM (α := α) Id β) :
    (it.scanWithPostcondition f init).toArray = it.toArray.run.scanlM (f · · |>.run) init := by
  rw [← toArray_toList]
  rw [IterM.toList_scanWithPostCondition, ← Array.scanlM_toList]
  rfl

@[simp]
theorem IterM.toArray_scanM {α β γ : Type w} {m : Type w → Type w'}
    [Monad m] [MonadAttach m] [LawfulMonad m] [WeaklyLawfulMonadAttach m]
    [Iterator α Id β] [Finite α Id]
    {f : γ → β → m γ} {init : γ} (it : IterM (α := α) Id β) :
    (it.scanM f init).toArray = it.toArray.run.scanlM f init := by
  simp [scanM]

@[simp]
theorem IterM.toArray_scan {α β γ : Type w}
    [Iterator α Id β] [Finite α Id]
    {f : γ → β → γ} {init : γ} (it : IterM (α := α) Id β) :
    (it.scan f init).toArray = it.toArray.run.scanl f init := by
  simp [scan, Id.run, PostconditionT.run_eq_map]
  rfl

theorem Iter.toArray_scanWithPostCondition {α β γ : Type w} {m : Type w → Type w'}
    [Monad m] [LawfulMonad m] [Iterator α Id β] [Finite α Id]
    {f : γ → β → PostconditionT m γ} {init : γ} (it : Iter (α := α) β) :
    (it.scanWithPostcondition f init).toArray = it.toArray.scanlM (f · · |>.run) init := by
  simp only [scanWithPostcondition, IterM.toArray_scanWithPostCondition]
  rfl

@[simp]
theorem Iter.toArray_scanM {α β γ : Type w} {m : Type w → Type w'}
    [Monad m] [MonadAttach m] [LawfulMonad m] [WeaklyLawfulMonadAttach m]
    [Iterator α Id β] [Finite α Id]
    {f : γ → β → m γ} {init : γ} (it : Iter (α := α) β) :
    (it.scanM f init).toArray = it.toArray.scanlM f init := by
  simp only [scanM, IterM.toArray_scanM]
  rfl

@[simp]
theorem Iter.toArray_scan {α β γ : Type w}
    [Iterator α Id β] [Finite α Id]
    {f : γ → β → γ} {init : γ} (it : Iter (α := α) β) :
    (it.scan f init).toArray = it.toArray.scanl f init := by
  rw [← toArray_toList]
  rw [Iter.toList_scan, ← Array.scanl_toList]
  rfl
end Std
