module
prelude
public import Batteries.Data.Iterators.Scan
public import Batteries.Data.List.Scan

public section


namespace Std.Iterators

private abbrev IterM.toScanIterM [Iterator α Id β] [Monad m] [MonadLiftT Id m]
    (it : IterM (α := α) Id β) (f : γ → β → m γ) (acc : γ) (emittedInit : Bool := false) : IterM (α := ScanM α Id m β γ f) m γ :=
  toIterM ⟨it.internalState, acc, emittedInit⟩ m γ

private theorem toList_scanM_emittedTrue [Iterator α Id β] [Finite α Id] [Monad m] [LawfulMonad m]
  [IteratorCollect α Id Id (β := β)] [LawfulIteratorCollect α Id Id (β := β)]
  {f : γ → β → m γ} {acc : γ} {it : IterM (α := α) Id β} 
  : (toIterM (m := m) (β := γ) (⟨it.internalState, acc, true⟩ : ScanM α Id m β γ f)).toList 
    = (return (← List.scanlM f acc (← it.toList)).tail) 
  := by
    induction it using IterM.inductSteps generalizing acc
    rename_i it ihy ihs
    repeat rw [IterM.toList_eq_match_step]
    simp_all [ScanM.instIterator, IterM.step, Iterator.step]
    apply bind_congr
    intro step
    match hstep : step.inflate with
    | ⟨.yield inner' out, hp⟩ =>
      simp_all [liftM, monadLift, Id.run, toIterM, Functor.map]
      apply bind_congr
      intro a
      rw [ihy hp, ← List.scanlM_cons_head_tail]
      simp
    | ⟨.skip inner', hp⟩ =>
      simp_all [liftM, monadLift, Id.run, toIterM];
    | ⟨.done, hp⟩ =>
      simp_all


@[local simp ←]
private theorem toIterM_eq_mk {state : ScanM α m n β γ f} :
    (toIterM state n γ : IterM n γ) = { internalState := state } := rfl


private theorem toList_scanM_emittedFalse [Iterator α Id β] [Finite α Id] [Monad m] [LawfulMonad m]
    [IteratorCollect α Id Id (β := β)] [LawfulIteratorCollect α Id Id (β := β)]
    {f : γ → β → m γ} {acc : γ} {it : IterM (α := α) Id β} :
    (toIterM (⟨it.internalState, acc, false⟩ : ScanM α Id m β γ f) m γ).toList = 
    List.scanlM f acc it.toList := by
  rw [IterM.toList_eq_match_step]
  simp only [Iterator.step, ScanM.instIterator, IterM.step]
  simp_all [liftM, monadLift, Id.run, toList_scanM_emittedTrue]
  rw [← List.scanlM_cons_head_tail f acc it.toList]
  simp

theorem IterM.toList_scanM [Iterator α Id β] [Finite α Id] [Monad m] [LawfulMonad m]
    [IteratorCollect α Id Id (β := β)] [LawfulIteratorCollect α Id Id (β := β)]
    {f : γ → β → m γ} {init : γ} (it : IterM (α := α) Id β) :
    (it.scanM f init).toList = List.scanlM f init it.toList := by
  simp only [IterM.scanM]
  rw [toList_scanM_emittedFalse]

end Std.Iterators
