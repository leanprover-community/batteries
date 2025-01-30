/-
Copyright (c) 2023 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import Lean.Util.Trace

open Lean

namespace Except

/-- Visualize an `Except` using a checkmark or a cross. -/
def emoji : Except ε α → String
  | .error _ => crossEmoji
  | .ok _ => checkEmoji

@[simp] theorem map_error {ε : Type u} (f : α → β) (e : ε) :
    f <$> (.error e : Except ε α) = .error e := rfl

@[simp] theorem map_ok {ε : Type u} (f : α → β) (x : α) :
    f <$> (.ok x : Except ε α) = .ok (f x) := rfl

/-- Map a function over an `Except` value, using a proof that the value is `.ok`. -/
def pmap {ε : Type u} {α β : Type v} (x : Except ε α) (f : (a : α) → x = .ok a → β) : Except ε β :=
  match x with
  | .error e => .error e
  | .ok a => .ok (f a rfl)

@[simp] theorem pmap_error {ε : Type u} {α β : Type v} (e : ε)
    (f : (a : α) → Except.error e = Except.ok a → β) :
    Except.pmap (.error e) f = .error e := rfl

@[simp] theorem pmap_ok {ε : Type u} {α β : Type v} (a : α)
    (f : (a' : α) → (.ok a : Except ε α) = .ok a' → β) :
    Except.pmap (.ok a) f = .ok (f a rfl) := rfl

@[simp] theorem pmap_id {ε : Type u} {α : Type v} (x : Except ε α) :
    x.pmap (fun a _ => a) = x := by cases x <;> simp

@[simp] theorem map_pmap (g : β → γ) (x : Except ε α) (f : (a : α) → x = .ok a → β) :
    g <$> x.pmap f = x.pmap fun a h => g (f a h) := by
  cases x <;> simp

end Except

namespace ExceptT

-- This will be redundant after nightly-2024-11-08.
attribute [ext] ExceptT.ext

@[simp] theorem run_mk {m : Type u → Type v} (x : m (Except ε α)) : (ExceptT.mk x).run = x := rfl
@[simp] theorem mk_run (x : ExceptT ε m α) : ExceptT.mk (ExceptT.run x) = x := rfl

@[simp]
theorem map_mk [Monad m] [LawfulMonad m] (f : α → β) (x : m (Except ε α)) :
    f <$> ExceptT.mk x = ExceptT.mk ((f <$> · ) <$> x) := by
  simp only [Functor.map, Except.map, ExceptT.map, map_eq_pure_bind]
  congr
  funext a
  split <;> simp

end ExceptT
