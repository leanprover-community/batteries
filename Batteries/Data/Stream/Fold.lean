/-
Copyright (c) 2024 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: François G. Dorais
-/
import Batteries.Data.Stream.WF

namespace Stream

/-! ### foldlM -/

/-- Folds a monadic function over a well founded stream from left to right. (Tail recursive.) -/
@[specialize] def foldlM [Monad m] [Stream.WF σ α] (f : β → α → m β) (init : β) (s : σ) : m β :=
  match _hint : next? s with
  | none => pure init
  | some (x, t) => f init x >>= (foldlM f · t)
termination_by s

theorem foldlM_init [Monad m] [Stream.WF σ α] {f : β → α → m β} {init : β} {s : σ}
    (h : next? s = none) : foldlM f init s = pure init := by rw [foldlM, h]

theorem foldlM_next [Monad m] [Stream.WF σ α] {f : β → α → m β} {init : β} {s t : σ} {x}
    (h : next? s = some (x, t)) : foldlM f init s = f init x >>= (foldlM f · t) := by rw [foldlM, h]

theorem foldlM_eq_foldlM_toList [Monad m] [Stream.WF σ α] (f : β → α → m β) (init : β) (s : σ) :
    foldlM f init s = (toList s).foldlM f init := by
  induction s using Stream.recWF generalizing init with
  | init h => simp only [foldlM_init h, toList_init h, List.foldlM_nil]
  | next h ih => simp only [foldlM_next h, toList_next h, List.foldlM_cons, ih]

/-! ### foldl -/

/-- Folds a function over a well founded stream from left to right. (Tail recursive.) -/
@[inline] def foldl [Stream.WF σ α] (f : β → α → β) (init : β) (s : σ) : β :=
  foldlM (m := Id) f init s

theorem foldl_init [Stream.WF σ α] {f : β → α → β} {init : β} {s : σ}
    (h : next? s = none) : foldl f init s = init := foldlM_init h

theorem foldl_next [Stream.WF σ α] {f : β → α → β} {init : β} {s t : σ}
    (h : next? s = some (x, t)) : foldl f init s = foldl f (f init x) t := foldlM_next h

theorem foldl_eq_foldl_toList [Stream.WF σ α] (f : β → α → β) (init : β) (s : σ) :
    foldl f init s = (toList s).foldl f init := by
  induction s using Stream.recWF generalizing init with
  | init h => simp only [foldl_init h, toList_init h, List.foldl_nil]
  | next h ih => simp only [foldl_next h, toList_next h, List.foldl_cons, ih]

/-! ### foldrM -/

/-- Folds a monadic function over a well founded stream from left to right. -/
@[specialize] def foldrM [Monad m] [Stream.WF σ α] (f : α → β → m β) (init : β) (s : σ) : m β :=
  match _hint : next? s with
  | none => pure init
  | some (x, t) => foldrM f init t >>= f x
termination_by s

theorem foldrM_init [Monad m] [Stream.WF σ α] {f : α → β → m β} {init : β} {s : σ}
    (h : next? s = none) : foldrM f init s = pure init := by rw [foldrM, h]

theorem foldrM_next [Monad m] [Stream.WF σ α] {f : α → β → m β} {init : β} {s t : σ}
    (h : next? s = some (x, t)) : foldrM f init s = foldrM f init t >>= f x := by rw [foldrM, h]

theorem foldrM_eq_foldrM_toList [Monad m] [LawfulMonad m] [Stream.WF σ α]
    (f : α → β → m β) (init : β) (s : σ) : foldrM f init s = (toList s).foldrM f init := by
  induction s using Stream.recWF with
  | init h => simp only [foldrM_init h, toList_init h, List.foldrM_nil]
  | next h ih => simp only [foldrM_next h, toList_next h, List.foldrM_cons, ih]

/-! ### foldr -/

/-- Folds a function over a well founded stream from left to right. -/
@[inline] def foldr [Stream.WF σ α] (f : α → β → β) (init : β) (s : σ) : β :=
  foldrM (m := Id) f init s

theorem foldr_init [Stream.WF σ α] {f : α → β → β} {init : β} {s : σ}
    (h : next? s = none) : foldr f init s = init := foldrM_init h

theorem foldr_next [Stream.WF σ α] {f : α → β → β} {init : β} {s t : σ}
    (h : next? s = some (x, t)) : foldr f init s = f x (foldr f init t) := foldrM_next h

theorem foldr_eq_foldr_toList [Stream.WF σ α] (f : α → β → β) (init : β) (s : σ) :
    foldr f init s = (toList s).foldr f init := by
  induction s using Stream.recWF with
  | init h => rw [foldr_init h, toList_init h, List.foldr_nil]
  | next h ih => rw [foldr_next h, toList_next h, List.foldr_cons, ih]

end Stream

theorem List.stream_foldlM_eq_foldlM [Monad m] (f : β → α → m β) (init : β) (l : List α) :
    Stream.foldlM f init l = l.foldlM f init := by
  induction l generalizing init with
  | nil => rw [Stream.foldlM_init, foldlM_nil]; rfl
  | cons x l ih => rw [Stream.foldlM_next, foldlM_cons]; congr; funext; apply ih; rfl

theorem List.stream_foldl_eq_foldl (f : β → α → β) (init : β) (l : List α) :
    Stream.foldl f init l = l.foldl f init := by
  induction l generalizing init with
  | nil => rw [Stream.foldl_init, foldl_nil]; rfl
  | cons x l ih => rw [Stream.foldl_next, foldl_cons]; congr; funext; apply ih; rfl

theorem List.stream_foldrM_eq_foldrM [Monad m] [LawfulMonad m] (f : α → β → m β) (init : β)
    (l : List α) : Stream.foldrM f init l = l.foldrM f init := by
  induction l generalizing init with
  | nil => rw [Stream.foldrM_init, foldrM_nil]; rfl
  | cons x l ih => rw [Stream.foldrM_next, foldrM_cons]; congr; funext; apply ih; rfl

theorem List.stream_foldr_eq_foldr (f : α → β → β) (init : β) (l : List α) :
    Stream.foldr f init l = l.foldr f init := by
  induction l generalizing init with
  | nil => rw [Stream.foldr_init, foldr_nil]; rfl
  | cons x l ih => rw [Stream.foldr_next, foldr_cons]; congr; funext; apply ih; rfl
