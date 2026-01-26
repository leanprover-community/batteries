/-
Copyright (c) 2025 Chad Sharp. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chad Sharp
-/

module

public section

namespace Std.Iterators


/--
  Internal state for the ScanM combinator
-/
structure ScanM (α : Type w) (m : Type w → Type w') (n : Type w → Type w'')
    (β : Type w) (γ : Type w) (f : γ → β → n γ) where
  /-- Inner iterator -/
  inner : α
  /-- Current accumulated value -/
  acc : γ
  /-- Whether we have emitted the initial value
    (and therefore should begin yielding from the iterator) -/
  emittedInit : Bool

namespace ScanM

variable {α β γ : Type w} {m : Type w → Type w'} {n : Type w → Type w''}
  {f : γ → β → n γ} [Iterator α m β]
/--
`it.IsPlausibleStep` is the proposition that `step` is a possible next step from the `scanM`
iterator `it`. This is mostly an internal implementation detail used to prove termination.
-/
inductive IsPlausibleStep (it : @IterM (ScanM α m n β γ f) n γ) :
    IterStep (@IterM (ScanM α m n β γ f) n γ) γ → Prop where

  /-- If we haven't emitted anything yet (emittedInit is false),
      we set it to true and do not update the internal iterator state
  -/
  | yieldInit {it' : IterM n γ} {out : γ} :
      it.internalState.emittedInit = false →
      it'.internalState.emittedInit = true →
      it'.internalState.inner = it.internalState.inner →
      IsPlausibleStep it (.yield it' out)
  /-- After `emittedInit` is set to true, we yield when the inner iterator does.
      The resulting state has emittedInit set to true and the updated internal iterator state.
  -/
  | yieldNext {innerIt' : IterM m β} {b : β} {it': IterM n γ} {out : γ}:
      it.internalState.emittedInit = true
      → Iterator.IsPlausibleStep ⟨it.internalState.inner⟩ (.yield innerIt' b)
      → it'.internalState.inner = innerIt'.internalState
      → it'.internalState.emittedInit = true
      → IsPlausibleStep it (.yield it' out)
  /-- After `emittedInit` is set to true, we skip when the inner iterator does.
      Our resulting state is identical, except with an updated inner iterator
  -/
  | skip {innerIt' : IterM m β} {it' : IterM n γ}:
      it.internalState.emittedInit = true
      → Iterator.IsPlausibleStep ⟨it.internalState.inner⟩ (.skip innerIt')
      → it' = ⟨{it.internalState with inner := innerIt'.internalState}⟩
      → IsPlausibleStep it (.skip it')
  /-- We are done when emittedInit is true and the internal iterator is done -/
  | done :
      it.internalState.emittedInit = true →
      Iterator.IsPlausibleStep (⟨it.internalState.inner⟩ : IterM m β) .done →
      IsPlausibleStep it .done

instance instIterator [Monad n] [MonadLiftT m n] :
    Iterator (ScanM α m n β γ f) n γ where

  IsPlausibleStep := IsPlausibleStep
  step it := do
    if h : it.internalState.emittedInit = false then
      pure <| .deflate <| .yield
        ⟨{ it.internalState with emittedInit := true }⟩
        it.internalState.acc
        (.yieldInit (by simpa using h) rfl rfl)
    else
      let innerIt := ⟨it.internalState.inner⟩
      match hs : (← liftM (Iterator.step innerIt)).inflate with
      | ⟨.yield inner' a, hp⟩ =>
        let newAcc ← f it.internalState.acc a
        pure <| .deflate <| .yield
          ⟨{it.internalState with inner := inner'.internalState, acc := newAcc}⟩
          newAcc
          (.yieldNext (by simpa using h) hp rfl (by simpa using h))
      | ⟨.skip inner', hp⟩ =>
        pure <| .deflate <| .skip
          ⟨{ it.internalState with inner := inner'.internalState }⟩
          (.skip (by simpa using h) hp rfl)
      | ⟨.done, hp⟩ =>
        pure <| .deflate <| .done (.done (by simpa using h) hp)

instance [Monad n] [MonadLiftT m n] :
    IteratorLoop (ScanM α m n β γ f) n n :=
  .defaultImplementation

instance {o : Type w → Type x} [Monad n] [MonadLiftT m n] [Monad o] :
    IteratorCollect (ScanM α m n β γ f) n o :=
  .defaultImplementation

/-- Finiteness relation for `ScanM`-/
private def finRel (scanIt' scanIt : @IterM (ScanM α m n β γ f) n γ) : Prop :=
  match scanIt.internalState.emittedInit, scanIt'.internalState.emittedInit with
  | false, true => True
  | true, true => (⟨scanIt'.internalState.inner⟩ : IterM m β).IsPlausibleSuccessorOf
      ⟨scanIt.internalState.inner⟩
  | _, _ => False

private theorem acc_finRel_emittedTrue [Finite α m (β := β)]
    (scanIt : @IterM (ScanM α m n β γ f) n γ)
    (hemit : scanIt.internalState.emittedInit = true) :
    Acc finRel scanIt := by
  generalize hgen : (⟨scanIt.internalState.inner⟩ : IterM m β) = innerIt
  induction Finite.wf.apply innerIt generalizing scanIt
  rename_i ih
  constructor
  intro scanIt' _
  by_cases scanIt'.internalState.emittedInit <;> simp_all only [finRel]
  exact ih ⟨scanIt'.internalState.inner⟩ ‹_› scanIt' ‹_› rfl

private theorem acc_finRel_emittedFalse [Finite α m (β := β)]
    (scanIt : @IterM (ScanM α m n β γ f) n γ)
    (hemit : scanIt.internalState.emittedInit = false) :
    Acc finRel scanIt := by
  constructor
  intro iter' _
  by_cases iter'.internalState.emittedInit
  . exact acc_finRel_emittedTrue _ ‹_›
  -- this leads to a contradiction
  . simp_all [finRel]

private theorem acc_finRel [Finite α m (β := β)] (scanIt : @IterM (ScanM α m n β γ f) n γ) :
    Acc finRel scanIt :=
  if h : scanIt.internalState.emittedInit
    then acc_finRel_emittedTrue _ ‹_›
    else acc_finRel_emittedFalse _ (by simp only [h])

private def instFinRel [Monad m] [Monad n] [MonadLiftT m n] [Finite α m (β := β)] :
    FinitenessRelation (ScanM α m n β γ f) n where
  rel := finRel
  wf := ⟨acc_finRel⟩
  subrelation := by
    rintro _ _ ⟨_, hsucc_eq, hplaus⟩
    cases hplaus
      <;> simp_all only [IterStep.successor, Option.some.injEq, reduceCtorEq]
      <;> subst hsucc_eq
      <;> simp_all only [finRel]
    . exact IterM.isPlausibleSuccessorOf_of_yield ‹_›
    . exact IterM.isPlausibleSuccessorOf_of_skip  ‹_›

instance [Finite α m (β := β)] [Monad m] [Monad n] [MonadLiftT m n] :
    Finite (ScanM α m n β γ f) n :=
  .of_finitenessRelation instFinRel

/-- Productiveness relation for ScanM -/
private def prodRel (scanIt' scanIt : @IterM (ScanM α m n β γ f) n γ) : Prop :=
  (⟨scanIt'.internalState.inner⟩ : IterM m β).IsPlausibleSkipSuccessorOf
    ⟨scanIt.internalState.inner⟩

private theorem acc_prodRel [Productive α m (β := β)]
    (scanIt : @IterM (ScanM α m n β γ f) n γ) :
    Acc prodRel scanIt := by
  generalize hgen : (⟨scanIt.internalState.inner⟩ : IterM m β) = innerIt
  induction Productive.wf.apply innerIt generalizing scanIt with grind only [prodRel, Acc]

private def instProdRel [Monad m] [Monad n] [MonadLiftT m n] [Productive α m (β := β)] :
    ProductivenessRelation (ScanM α m n β γ f) n where
  rel := prodRel
  wf := ⟨acc_prodRel⟩
  subrelation := by
    intro _ _ hsucc
    cases hsucc <;> simp_all [prodRel, IterM.IsPlausibleSkipSuccessorOf]

instance [Productive α m (β := β)] [Monad m] [Monad n] [MonadLiftT m n] :
    Productive (ScanM α m n β γ f) n :=
  .of_productivenessRelation instProdRel

end ScanM

section Combinators
variable {α β γ : Type w}

section Monadic
variable {m : Type w → Type w'}

/--
If `it` is an iterator, then `it.scanM f init` is another iterator that folds a
monadic function `f` over the values emitted by `it`, producing an iterator of
partial results. The first value emitted by the resulting iterator is always
`pure init`.

The base iterator `it` being monadic in `m`, `f` can return values in any monad `n`
for which a `MonadLiftT m n` instance is available.

If `f` is pure, then the simpler variant `it.scan` can be used instead.

**Marble diagram (without monadic effects)**

```text
it         -------a--b--c--⊥
it.scanM   init---a'-b'-c'-⊥
```
(given that `a' ← f init a`, `b' ← f a' b`, `c' ← f b' c`)

**Termination properties:**
* `Finite` instance: only if `it` is finite.
* `Productive` instance: only if `it` is productive.

** Performance:**

For each value emitted by the base iterator `it`, this combinator calls `f`.
-/
@[inline, expose]
def IterM.scanM {n : Type w → Type w''} (f : γ → β → n γ) (init : γ) (it : IterM (α := α) m β) :=
  toIterM { inner := it.internalState, acc := init, emittedInit := false : ScanM α m n β γ f } n γ

/--
If `it` is an iterator, then `it.scan f init` is another iterator that folds a
pure function `f` over the values emitted by `it`, producing an iterator of
partial results. The first value emitted by the resulting iterator is always
`init`.

If `f` is monadic, `it.scanM` can be used instead.

**Marble diagram**

```text
it        -------a--b--c--⊥
it.scan   init---a'-b'-c'-⊥
```
(given that `a' = f init a`, `b' = f a' b`, `c' = f b' c`)

**Termination properties:**
* `Finite` instance: only if `it` is finite.
* `Productive` instance: only if `it` is productive.

** Performance:**

For each value emitted by the base iterator `it`, this combinator calls `f`.
-/

@[inline, expose]
def IterM.scan [Monad m]
    (f : γ → β → γ) (init : γ) (it : IterM (α := α) m β) :=
  IterM.scanM (m := m) (n := m) (pure <| f · ·) init it

end Monadic

@[inline, expose, inherit_doc IterM.scanM]
def Iter.scanM {n : Type w → Type w''} (f : γ → β → n γ) (init : γ) (it : Iter (α := α) β) :=
  IterM.scanM f init it.toIterM

@[inline, expose, inherit_doc IterM.scan]
def Iter.scan (f : γ → β → γ) (init : γ) (it : Iter (α := α) β) :=
  Iter.scanM (n := Id) (pure <| f · ·) init it |>.toIter

end Combinators
end Std.Iterators
