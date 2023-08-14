/-
Copyright (c) 2022 James Gallicchio. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: James Gallicchio
-/

import Std.Classes.Collections.Fold

/-! ## External Iterators -/

namespace Std

/--
Exposes `toIterator`, which gives an object that can traverse
the collection one item at a time.
-/
class Iterable (C : Type u) (τ : outParam (Type v)) where
  /-- The iterator object type. -/
  ρ : Type w
  /-- Convert a collection to its iteration object. -/
  toIterator : C → ρ
  /-- ρ is a stream of τs -/
  [toStream : Stream ρ τ]

namespace Iterable

instance [I : Iterable C τ] : Stream (Iterable.ρ C) τ := I.toStream

instance [Iterable C τ] : ForIn m C τ where
  forIn c acc f := do
  let mut iter := toIterator c
  let mut done := false
  let mut res := acc
  while !done do
    match Stream.next? iter with
    | none =>
      done := true
    | some (x, iter') =>
      match ← f x res with
      | ForInStep.yield y =>
        res := y
        iter := iter'
      | ForInStep.done y =>
        res := y
        done := true
  return res

end Iterable

/--
An `Iterable` for which the iterator object has some well-ordered
notion of size, which decreases at each `Stream.next?`. This is used to
automatically generate `Fold` implementations for `Iterable`s.
-/
class WFIterable (C : Type u) (τ : outParam (Type v)) extends Iterable C τ where
  /-- Iterator type `ρ` has a well-founded relation. -/
  wf : WellFoundedRelation ρ
  /-- Domain under which the iterator is well-founded. -/
  dom : ρ → Prop
  /-- `toIterator` generates an iterator within `dom`. -/
  h_toIterator : ∀ c, dom (toIterator c)
  /-- Assuming the iterator is within `dom`, `step` respects
    the well-founded relation and stays within `dom`. -/
  h_step : ∀ r, dom r →
    ∀ x r', Stream.next? r = some (x, r') →
      wf.rel r' r ∧ dom r'

attribute [instance] WFIterable.wf

namespace WFIterable

/-- Fold function for well-founded iterable collections. -/
def fold [WFIterable C τ] {β} (f : _ → _ → _) (init c) :=
  let rec loop (r : Iterable.ρ C) (hr : WFIterable.dom r) (acc : β) :=
    match h : Stream.next? r with
    | none => acc
    | some (x, r') =>
      have wf_step := WFIterable.h_step r hr x r' h
      have := wf_step.1
      loop r' wf_step.2 (f acc x)
  loop (Iterable.toIterator c) (WFIterable.h_toIterator c) init
termination_by loop r _ _ => r

@[default_instance]
instance [WFIterable C τ] : Fold C τ where
  fold := @fold _ _ _

instance : WFIterable (List α) α where
  ρ := List α
  toIterator L := L
  toStream :=
    ⟨fun L => match L with
    | [] => none
    | x::xs => some (x,xs)⟩
  dom _ := True
  wf := invImage List.length Nat.lt_wfRel
  h_toIterator _ := by simp
  h_step := by
    intro r _ x r' h
    simp [WellFoundedRelation.rel, InvImage, Nat.lt_wfRel]
    simp [Stream.next?] at h
    split at h
    . contradiction
    . cases h
      simp [List.length]
      apply Nat.lt_succ_self

/-- Fold with dependent motive. -/
def foldD [WFIterable C τ]
  (motive : (r : Iterable.ρ C) → Sort u)
  (c : C)
  (f : (r : Iterable.ρ C) → WFIterable.dom r →
        (x : τ) → (r' : Iterable.ρ C) → Stream.next? r = some (x,r') →
        motive r → motive r')
  (init : motive (Iterable.toIterator c))
  : Σ' r, PProd (WFIterable.dom r ∧ Stream.next? r = none) (motive r) :=
  let rec loop (r : Iterable.ρ C) (hr : WFIterable.dom r)
    (acc : motive r) :=
    match h : Stream.next? r with
    | none => ⟨r, ⟨hr, h⟩, acc⟩
    | some (x, r') =>
      have := WFIterable.h_step r hr x r' h
      have _ := this.1
      loop r' this.2 (f r hr x r' h acc)
  loop (Iterable.toIterator c) (WFIterable.h_toIterator c) init
termination_by loop r _ _ => r

/-- `forIn` implementation -/
def forIn [WFIterable C τ] {β} [Monad m]
      (c : C) (b : β) (f : τ → β → m (ForInStep β)) : m β :=
  let rec loop (r : Iterable.ρ C) (hr : WFIterable.dom r) (acc : β) : m β :=
    match h : Stream.next? r with
    | none => pure acc
    | some (x, r') =>
    bind (f x acc) fun
    | ForInStep.done acc => pure acc
    | ForInStep.yield acc =>
      have := WFIterable.h_step r hr x r' h
      have _ := this.1
      loop r' this.2 acc
  loop (Iterable.toIterator c) (WFIterable.h_toIterator c) b
termination_by loop r _ _ => r

/-- Dependent `forIn`; allows for proving iteration invariants.

TODO: Can generalize motive universe, but should we?
-/
def forInD [WFIterable.{uC, uT, uR} C τ] [Monad m]
  (motive : (r : Iterable.ρ C) → Type uR)
  (c : C)
  (b : motive (Iterable.toIterator c))
  (f : (r : Iterable.ρ C) → WFIterable.dom r →
        (x : τ) → (r' : Iterable.ρ C) → Stream.next? r = some (x,r') →
        motive r → m (motive r'))
  : m (Σ' r, PProd (WFIterable.dom r ∧ Stream.next? r = none) (motive r)) :=
  let rec loop (r : Iterable.ρ C) (hr : WFIterable.dom r) (acc : motive r) :=
    match h : Stream.next? r with
    | none => pure ⟨r, ⟨hr, h⟩, acc⟩
    | some (x, r') =>
    have := WFIterable.h_step r hr x r' h
    bind (f r hr x r' h acc) fun acc =>
      have _ := this.1
      loop r' this.2 acc
  loop (Iterable.toIterator c) (WFIterable.h_toIterator c) b
termination_by loop r _ _ => r

/-- `forIn` with an iteration invariant. Used for definining loop invariant syntax. -/
def forInWithInv [WFIterable.{uC, uT, uR} C τ] [Monad m]
  {β : Type uR} (inv : (r : Iterable.ρ C) → β → Prop)
  (c : C)
  (b : β) (hb : inv (Iterable.toIterator c) b)
  (f : (r : Iterable.ρ C) → WFIterable.dom r →
        (x : τ) → (r' : Iterable.ρ C) → Stream.next? r = some (x,r') →
        (acc : β) → inv r acc → m ((b : β) ×' inv r' b))
  : m (Σ' r, PProd (WFIterable.dom r ∧ Stream.next? r = none) ((b : β) ×' inv r b))
  := forInD (motive := fun r => (b : β) ×' inv r b)
      c ⟨b,hb⟩ (fun r hd x r' hr ⟨acc,hacc⟩ => f r hd x r' hr acc hacc)
