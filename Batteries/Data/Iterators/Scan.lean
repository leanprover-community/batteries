/-
Copyright (c) 2025 Chad Sharp. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chad Sharp
-/

module
import Batteries.Data.Bool

public section
namespace Std.Iterators.Types

/--
  Internal state for the ScanM combinator
-/
structure ScanM  {β γ : Type w} {n : Type w → Type w''}
     (α : Type w) (m : Type w → Type w') (f : γ → β → PostconditionT n γ)
    [Monad m] [Monad n] [MonadLiftT m n] [Iterator α m β] where
  /-- Inner iterator -/
  inner : IterM (α := α) m β
  /-- Current accumulated value -/
  acc : γ
  /-- Whether we need to emit the accumulator (i.e. whether this is the first step)-/
  yieldAcc : Bool

/-- Internal implementation of the `scanM` combinator. See `IterM.scanM` for the public API. -/
@[expose]
public def IterM.InternalCombinators.scanM [Monad m] [Monad n] [MonadLiftT m n] [Iterator α m β]
    (f : γ → β → PostconditionT n γ) (acc : γ) (yieldAcc : Bool) (it : IterM (α := α) m β) :
    IterM (α := ScanM α m f) n γ :=
  .mk ⟨it, acc, yieldAcc⟩ n γ

namespace ScanM
variable {α β γ : Type w} {m : Type w → Type w'} {n : Type w → Type w''}
  {f : γ → β → PostconditionT n γ} [Monad m] [Monad n] [MonadLiftT m n] [Iterator α m β]

/--
`it.IsPlausibleStep` is the proposition that `step` is a possible next step from the `scanM`
iterator `it`. This is mostly an internal implementation detail used to prove termination.
-/
inductive IsPlausibleStep (it : IterM (α := ScanM α m f) n γ) :
    IterStep (IterM (α := ScanM α m f) n γ) γ → Prop where
  /-- When `yieldAcc` is true, the step yields the current accumulator and
      the successor iterator is identical except with `yieldAcc` set to false.
  -/
  | yieldInit :
      it.internalState.yieldAcc = true →
      IsPlausibleStep it (.yield
        (IterM.InternalCombinators.scanM f it.internalState.acc false it.internalState.inner)
         it.internalState.acc)
  /-- When `yieldAcc` is false and the inner iterator yields `b` with successor `it'`,
      the step yields an `out` satisfying `(f acc b).Property out`, and the successor
      wraps `it'` with `out` as the new accumulator.
  -/
  | yieldNext :
      it.internalState.yieldAcc = false →
      it.internalState.inner.IsPlausibleStep (.yield it' b) →
      (f it.internalState.acc b).Property out →
      IsPlausibleStep it (.yield (IterM.InternalCombinators.scanM f out false it') out)
  /-- When `yieldAcc` is false and the inner iterator skips with successor `it'`,
      the step skips and the successor wraps `it'` with the same accumulator.
  -/
  | skip :
      it.internalState.yieldAcc = false →
      it.internalState.inner.IsPlausibleStep (.skip it') →
      IsPlausibleStep it
      (.skip (IterM.InternalCombinators.scanM f it.internalState.acc false it'))
  /-- When `yieldAcc` is false and the inner iterator is done, the step is done. -/
  | done :
      it.internalState.yieldAcc = false →
      it.internalState.inner.IsPlausibleStep .done →
      IsPlausibleStep it .done

instance instIterator : Iterator (ScanM α m f) n γ where
  IsPlausibleStep := ScanM.IsPlausibleStep
  step it := do
      if h : it.internalState.yieldAcc = true then
        pure <| .deflate <| .yield
          (IterM.InternalCombinators.scanM f it.internalState.acc false it.internalState.inner)
          it.internalState.acc
          (.yieldInit h)
      else
        match (← it.internalState.inner.step).inflate with
        | .yield inner' b hp => do
          let ⟨newAcc, h_acc⟩ ← (f it.internalState.acc b).operation
          pure <| .deflate <| .yield
            (IterM.InternalCombinators.scanM f newAcc false inner')
            newAcc
            (.yieldNext (by simpa using h) hp h_acc)
        | .skip inner' hp =>
          pure <| .deflate <| .skip
            (IterM.InternalCombinators.scanM f it.internalState.acc false inner')
            (.skip (by simpa using h) hp)
        | .done hp =>
          pure <| .deflate <| .done (.done (by simpa using h) hp)

private def FinRel [Finite α m] :
    IterM (α := ScanM α m f) n γ → IterM (α := ScanM α m f) n γ → Prop :=
  InvImage
    (Prod.Lex (· < ·) IterM.IsPlausibleSuccessorOf)
    (fun it => (it.internalState.yieldAcc, it.internalState.inner))

private theorem FinRel.of_yieldAcc [Finite α m] {it it' : IterM (α := ScanM α m f) n γ}
    (h' : it'.internalState.yieldAcc = false) (h : it.internalState.yieldAcc = true) :
    FinRel it' it := by
  apply Prod.Lex.left
  simp [*, LT.lt]

private theorem FinRel.of_inner [Finite α m] {it it' : IterM (α := ScanM α m f) n γ}
    (h : it'.internalState.yieldAcc = it.internalState.yieldAcc)
    (h' : it'.internalState.inner.IsPlausibleSuccessorOf it.internalState.inner) :
    FinRel it' it := by
  simp_all [FinRel, InvImage, Prod.Lex.right]

private def instFinitenessRelation [Finite α m] : FinitenessRelation (ScanM α m f) n where
  Rel := FinRel
  wf := by
    apply InvImage.wf
    refine ⟨fun (a, b) => Prod.lexAccessible (WellFounded.apply ?_ a) (WellFounded.apply ?_) b⟩
    · exact Bool.lt_wfRel.wf
    · exact Finite.wf
  subrelation h := by
    obtain ⟨step, hstep, hplaus⟩ := h
    cases hplaus <;> cases hstep
    case yieldInit => simp_all [FinRel.of_yieldAcc, IterM.InternalCombinators.scanM]
    all_goals
      apply FinRel.of_inner <;> simp_all only [IterM.InternalCombinators.scanM, IterM.mk]
    . exact IterM.isPlausibleSuccessorOf_of_yield ‹_›
    . exact IterM.isPlausibleSuccessorOf_of_skip ‹_›

instance instFinite [Finite α m] : Finite (ScanM α m f) n :=
  .of_finitenessRelation instFinitenessRelation

private def instProductivenessRelation [Productive α m] :
    ProductivenessRelation (ScanM α m f) n where
  Rel := InvImage IterM.IsPlausibleSkipSuccessorOf (ScanM.inner ∘ IterM.internalState)
  wf := InvImage.wf _ Productive.wf
  subrelation h := by cases h; assumption

instance instProductive [Productive α m] : Productive (ScanM α m f) n :=
  .of_productivenessRelation instProductivenessRelation

instance instIteratorLoop : IteratorLoop (ScanM α m f) n m :=
  .defaultImplementation

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

(given that `a' ← f i a'`, `ab' ← f a' b`, `abc' ← f ab' c'`)

**Termination properties:**

* `Finite` instance: only if `it` is finite
* `Productive` instance: only if `it` is productive

**Performance:**

For each value emitted by the base iterator `it`, this combinator calls `f`.
-/
@[inline, expose]
def IterM.scanWithPostcondition [Monad m] [Monad n] [MonadLiftT m n] [Iterator α m β]
    (f : γ → β → PostconditionT n γ) (acc : γ) (it : IterM (α := α) m β) :=
  IterM.InternalCombinators.scanM (n := n) f acc true it

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

(given that `a' ← f i a`, `ab' ← f a' b`, `abc' ← f ab' c`)

**Termination properties:**

* `Finite` instance: only if `it` is finite
* `Productive` instance: only if `it` is productive

**Performance:**

For each value emitted by the base iterator `it`, this combinator calls `f`.
-/
@[inline, expose]
def IterM.scanM [MonadAttach n] [Monad m] [Monad n] [MonadLiftT m n] [Iterator α m β]
    (f : γ → β → n γ) (acc : γ) (it : IterM (α := α) m β) :=
  it.scanWithPostcondition (PostconditionT.attachLift <| f · ·) acc

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
def IterM.scan [Iterator α m β] [Monad m] (f : γ → β → γ) (acc : γ) (it : IterM (α := α) m β) :=
  (it.scanWithPostcondition (pure <| f · ·) acc : IterM m γ)


@[inline, expose, inherit_doc IterM.scanWithPostcondition]
def Iter.scanWithPostcondition [Monad m] [Iterator α Id β]
    (f : γ → β → PostconditionT m γ) (acc : γ) (it : Iter (α := α) β) :=
  it.toIterM.scanWithPostcondition f acc

@[inline, expose, inherit_doc IterM.scanM]
def Iter.scanM [MonadAttach n] [Monad n] [Iterator α Id β]
    (f : γ → β → n γ) (acc : γ) (it : Iter (α := α) β) :=
  it.toIterM.scanM f acc

@[inline, expose, inherit_doc IterM.scan]
def Iter.scan [Iterator α Id β] (f : γ → β → γ) (acc : γ) (it : Iter (α := α) β) :=
  it.toIterM.scan f acc |>.toIter
end Std
