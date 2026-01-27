/-
Copyright (c) 2025 Chad Sharp. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chad Sharp
-/

module

public section
namespace Std.Iterators.Types

/--
  Internal state for the ScanM combinator
-/
structure ScanM (α : Type w) (m : Type w → Type w') (n : Type w → Type w'')
    (β : Type w) (γ : Type w) (lift : ⦃α : Type w⦄ → m α → n α)
    (f : γ → β → PostconditionT n γ)  where
  /-- Inner iterator -/
  inner : IterM (α := α) m β
  /-- Current accumulated value -/
  acc : γ
  /-- Whether we need to emit the initial value
    (and therefore have not yet begun yielding from the iterator) -/
  needsInit : Bool

/-- Internal implementation of the `scanM` combinator. See `IterM.scanM` for the public API. -/
@[expose]
public def IterM.InternalCombinators.scanM (lift : ⦃α : Type w⦄ → m α → n α )
    (f : γ → β → PostconditionT n γ) (acc : γ) (needsInit : Bool) (it : IterM (α := α) m β) :
    IterM (α := ScanM α m n β γ lift f) n γ :=
  .mk ⟨it, acc, needsInit⟩ n γ

namespace ScanM
variable {α β γ : Type w} {m : Type w → Type w'} {n : Type w → Type w''}
  {f : γ → β → PostconditionT n γ} {lift : ⦃α : Type w⦄ → m α → n α} [Iterator α m β]

/--
`it.IsPlausibleStep` is the proposition that `step` is a possible next step from the `scanM`
iterator `it`. This is mostly an internal implementation detail used to prove termination.
-/
inductive IsPlausibleStep (it : @IterM (ScanM α m n β γ lift f) n γ) :
    IterStep (@IterM (ScanM α m n β γ lift f) n γ) γ → Prop where
  /-- If we haven't emitted anything yet (needsInit is true),
      we set it to false and do not update the internal iterator state
  -/
  | yieldInit :
      it.internalState.needsInit = true →
      IsPlausibleStep it (.yield
        (IterM.InternalCombinators.scanM
         lift f it.internalState.acc false it.internalState.inner)
         it.internalState.acc)
  /-- After `needsInit` is set to false, we yield when the inner iterator does.
      The resulting state has needsInit set to false and the updated internal iterator state.
  -/
  | yieldNext : ∀ {it' b out},
      it.internalState.needsInit = false →
      it.internalState.inner.IsPlausibleStep (.yield it' b) →
      (f it.internalState.acc b).Property out →
      IsPlausibleStep it (.yield (IterM.InternalCombinators.scanM lift f out false it') out)
  /-- After `needsInit` is set to false, we skip when the inner iterator does.
      Our resulting state is identical, except with an updated inner iterator
  -/
  | skip : ∀ {it'},
      it.internalState.needsInit = false →
      it.internalState.inner.IsPlausibleStep (.skip it') →
      IsPlausibleStep it
      (.skip (IterM.InternalCombinators.scanM lift f it.internalState.acc false it'))
  /-- We are done when needsInit is false and the internal iterator is done -/
  | done :
      it.internalState.needsInit = false →
      it.internalState.inner.IsPlausibleStep .done →
      IsPlausibleStep it .done

instance instIterator {α β γ : Type w} {m : Type w → Type w'}
    {n : Type w → Type w''} {lift : ⦃α : Type w⦄ → m α → n α} {f : γ → β → PostconditionT n γ}
    [Iterator α m β] [Monad n] :
    Iterator (ScanM α m n β γ lift f) n γ where
  IsPlausibleStep := ScanM.IsPlausibleStep
  step it :=
    letI : MonadLift m n := ⟨lift (α := _)⟩
    do
      if h : it.internalState.needsInit = true then
        pure <| .deflate <| .yield
          (IterM.InternalCombinators.scanM lift f it.internalState.acc false it.internalState.inner)
          it.internalState.acc
          (by exact .yieldInit h)
      else
        match (← it.internalState.inner.step).inflate with
        | .yield inner' b hp => do
          let ⟨newAcc, h_acc⟩ ← (f it.internalState.acc b).operation
          pure <| .deflate <| .yield
            (IterM.InternalCombinators.scanM lift f newAcc false inner')
            newAcc
            (by exact .yieldNext (by simpa using h) hp h_acc)
        | .skip inner' hp =>
          pure <| .deflate <| .skip
            (IterM.InternalCombinators.scanM lift f it.internalState.acc false inner')
            (by exact .skip (by simpa using h) hp)
        | .done hp =>
          pure <| .deflate <| .done (by exact .done (by simpa using h) hp)


namespace Finite
private def Rel [Monad n] [Finite α m] :
    IterM (α := ScanM α m n β γ lift f) n γ → IterM (α := ScanM α m n β γ lift f) n γ → Prop :=
  InvImage
    (Prod.Lex
      (· < ·)
      IterM.IsPlausibleSuccessorOf)
    (fun it => (it.internalState.needsInit.toNat, it.internalState.inner))

private theorem Rel.of_needsInit [Monad n] [Finite α m]
    {it it' : IterM (α := ScanM α m n β γ lift f) n γ}
    (h' : it'.internalState.needsInit = false)
    (h : it.internalState.needsInit = true) :
    Rel it' it := by
  apply Prod.Lex.left
  simp_all

private theorem Rel.of_inner [Monad n] [Finite α m]
    {it it' : IterM (α := ScanM α m n β γ lift f) n γ}
    (h : it'.internalState.needsInit = it.internalState.needsInit)
    (h' : it'.internalState.inner.IsPlausibleSuccessorOf it.internalState.inner) :
    Rel it' it := by
  simp only [Rel, InvImage, h]
  exact Prod.Lex.right _ h'

private def instFinitenessRelation {α β γ : Type w} {m : Type w → Type w'}
    {n : Type w → Type w''} [Monad n] [Iterator α m β] {lift : ⦃α : Type w⦄ → m α → n α}
    {f : γ → β → PostconditionT n γ} [Finite α m] :
    FinitenessRelation (ScanM α m n β γ lift f) n where
  Rel := Rel
  wf := by
    apply InvImage.wf
    refine ⟨fun (a, b) => Prod.lexAccessible (WellFounded.apply ?_ a) (WellFounded.apply ?_) b⟩
    · exact Nat.lt_wfRel.wf
    · exact Finite.wf
  subrelation {it it'} h := by
    obtain ⟨step, hstep, hplaus⟩ := h
    cases hplaus <;> cases hstep
    case yieldInit =>
      simp_all [Rel.of_needsInit, IterM.InternalCombinators.scanM]
    all_goals
      apply Rel.of_inner <;> simp_all only [IterM.InternalCombinators.scanM, IterM.mk]
    . exact IterM.isPlausibleSuccessorOf_of_yield ‹_›
    . exact IterM.isPlausibleSuccessorOf_of_skip ‹_›
end Finite

instance instFinite [Finite α m (β := β)] [Monad n] :
    Finite (ScanM α m n β γ lift f) n :=
  .of_finitenessRelation Finite.instFinitenessRelation

private def instProductivenessRelation [Monad n] [Productive α m] :
    ProductivenessRelation (ScanM α m n β γ lift f) n where
  Rel := InvImage IterM.IsPlausibleSkipSuccessorOf (ScanM.inner ∘ IterM.internalState)
  wf := InvImage.wf _ Productive.wf
  subrelation {it it'} h := by cases h; assumption

instance instProductive [Monad n] [Productive α m] :
    Productive (ScanM α m n β γ lift f) n :=
  Productive.of_productivenessRelation instProductivenessRelation

end ScanM
end Std.Iterators.Types

namespace Std
open Std.Iterators.Types Std.Iterators

/--
*Note: This is a very general combinator that requires an advanced understanding of monads,
dependent types and termination proofs. The variant `scanM` is easier to use and sufficient
for most use cases.*

If `it` is an iterator, then `it.scanWithPostcondition f acc` is another iterator that applies a
monadic function `f` to accumulate values emitted by `it`. It first emits the initial accumulator
`acc`, then for each value `b` emitted by `it`, it computes `f acc b` and emits the result.

`f` is expected to return `PostconditionT n γ`. The base iterator `it` being monadic in
`m`, `n` can be different from `m`, but `it.scanWithPostcondition f acc` expects a `MonadLiftT m n`
instance. The `PostconditionT` transformer allows the caller to intrinsically prove properties about
`f`'s return value in the monad `n`, enabling termination proofs depending on the specific behavior
of `f`.

**Marble diagram (without monadic effects):**

```text
it                          ---a ---b ---c ---⊥
it.scanWithPostcondition    -i -a'-ab'-abc'---⊥
```

(given that `f i a = pure a'`, `f a' b = pure ab'`, `f ab' c = pure abc'`)

**Termination properties:**

* `Finite` instance: only if `it` is finite
* `Productive` instance: only if `it` is productive

**Performance:**

For each value emitted by the base iterator `it`, this combinator calls `f`.
-/
@[inline, expose]
def IterM.scanWithPostcondition {α β γ : Type w} {m : Type w → Type w'} {n : Type w → Type w''}
    [MonadLiftT m n] (f : γ → β → PostconditionT n γ) (acc : γ)
    (it : IterM (α := α) m β) :=
  IterM.InternalCombinators.scanM (n := n) (fun ⦃_⦄ => monadLift) f acc true it

/--
If `it` is an iterator, then `it.scanM f acc` is another iterator that applies a monadic
function `f` to accumulate values emitted by `it`. It first emits the initial accumulator
`acc`, then for each value `b` emitted by `it`, it computes `f acc b` and emits the result.

The base iterator `it` being monadic in `m`, `f` can return values in any monad `n` for which a
`MonadLiftT m n` instance is available.

If `f` is pure, then the simpler variant `it.scan` can be used instead.

**Marble diagram (without monadic effects):**

```text
it           ---a ---b ---c ---⊥
it.scanM     -i -a'-ab'-abc'---⊥
```

(given that `f i a = pure a'`, `f a' b = pure ab'`, `f ab' c = pure abc'`)

**Termination properties:**

* `Finite` instance: only if `it` is finite
* `Productive` instance: only if `it` is productive

**Performance:**

For each value emitted by the base iterator `it`, this combinator calls `f`.
-/
@[inline, expose]
def IterM.scanM {α β γ : Type w} {m : Type w → Type w'} {n : Type w → Type w''}
    [MonadAttach n] [MonadLiftT m n]
    (f : γ → β → n γ) (acc : γ) (it : IterM (α := α) m β) :=
  it.scanWithPostcondition (fun a b => PostconditionT.attachLift (f a b)) acc

/--
If `it` is an iterator, then `it.scan f acc` is another iterator that applies a
function `f` to accumulate values emitted by `it`. It first emits the initial accumulator
`acc`, then for each value `b` emitted by `it`, it computes `f acc b` and emits the result.

In situations where `f` is monadic, use `scanM` instead.

**Marble diagram:**

```text
it         ---a ---b ---c ---⊥
it.scan    -i -a'-ab'-abc'---⊥
```

(given that `f i a = a'`, `f a' b = ab'`, `f ab' c = abc'`)

**Termination properties:**

* `Finite` instance: only if `it` is finite
* `Productive` instance: only if `it` is productive

**Performance:**

For each value emitted by the base iterator `it`, this combinator calls `f`.
-/
@[inline, expose]
def IterM.scan {α β γ : Type w} {m : Type w → Type w'}
    [Monad m] (f : γ → β → γ) (acc : γ) (it : IterM (α := α) m β) :=
  (it.scanWithPostcondition (fun a b => pure (f a b)) acc : IterM m γ)


@[inline, expose, inherit_doc IterM.scanM]
def Iter.scanWithPostcondition {α β γ : Type w} {m : Type w → Type w'}
    [Monad m] (f : γ → β → PostconditionT m γ) (acc : γ)
    (it : Iter (α := α) β) :=
  letI : MonadLift Id m := ⟨pure⟩;
  it.toIterM.scanWithPostcondition f acc

@[inline, expose, inherit_doc IterM.scanM]
def Iter.scanM {α β γ : Type w} {n : Type w → Type w''}
    [Monad n] [MonadAttach n]
    (f : γ → β → n γ) (acc : γ) (it : Iter (α := α) β) :=
  letI : MonadLift Id n := ⟨pure⟩
  it.toIterM.scanM f acc

@[inline, expose, inherit_doc IterM.scan]
def Iter.scan {α β γ : Type w}
    (f : γ → β → γ) (acc : γ) (it : Iter (α := α) β) :=
  it.toIterM.scan f acc |>.toIter
end Std
