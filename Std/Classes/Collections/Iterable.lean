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
class Iterable (C : Type u) (τ : Type v) where
  /-- The iterator object type. -/
  ρ : Type w
  /-- Convert a collection to its iteration object. -/
  toIterator : C → ρ
  /-- Step the iterator to its next value. -/
  step : ρ → Option (τ × ρ)

instance [Iterable C τ] : Stream (Iterable.ρ C τ) τ where
  next? := Iterable.step

instance [Iterable C τ] : ForIn m C τ where
  forIn c acc f := do
  let mut iter := Iterable.toIterator c
  let mut done := false
  let mut res := acc
  while !done do
    match Iterable.step iter with
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

/--
An `Iterable` for which the iterator object has some well-ordered
notion of size, which decreases at each `step`. This is used to
automatically generate `Fold` implementations for `Iterable`s.
-/
class FinIterable (C : Type u) (τ : Type v) extends Iterable C τ where
  /-- Iterator type `ρ` has a well-founded relation. -/
  wf : WellFoundedRelation ρ
  /-- Iterable `step` function respects the well-founded relation. -/
  h_step : ∀ r x r', Iterable.step r = some (x, r') → wf.rel r' r

attribute [instance] FinIterable.wf

@[default_instance]
instance [FinIterable C τ] : Fold C τ where
  fold β f init c :=
    let rec loop (r : Iterable.ρ C τ) (acc : β) :=
      match h : Iterable.step r with
      | none => acc
      | some (x, r') =>
        have : FinIterable.wf.rel r' r :=
          FinIterable.h_step r x r' h
        loop r' (f acc x)
    loop (Iterable.toIterator c) init
termination_by loop r _ => r
