/-
Copyright (c) 2017 Robert Y. Lewis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Y. Lewis, Keeley Hoek, Mario Carneiro, François G. Dorais, Quang Dao
-/
import Batteries.Tactic.Alias
import Batteries.Data.Array.Basic
import Batteries.Data.List.Basic

namespace Fin

/-- `min n m` as an element of `Fin (m + 1)` -/
def clamp (n m : Nat) : Fin (m + 1) := ⟨min n m, Nat.lt_succ_of_le (Nat.min_le_right ..)⟩

@[deprecated (since := "2024-11-15")]
alias enum := Array.finRange

@[deprecated (since := "2024-11-15")]
alias list := List.finRange

/-- Heterogeneous monadic fold over `Fin n` from right to left:
```
Fin.foldrM n f xₙ = do
  let xₙ₋₁ : α (n-1) ← f (n-1) xₙ
  let xₙ₋₂ : α (n-2) ← f (n-2) xₙ₋₁
  ...
  let x₀ : α 0 ← f 0 x₁
  pure x₀
```
This is the dependent version of `Fin.foldrM`. -/
@[inline] def dfoldrM [Monad m] (n : Nat) (α : Fin (n + 1) → Type _)
    (f : ∀ (i : Fin n), α i.succ → m (α i.castSucc)) (init : α (last n)) : m (α 0) :=
  loop n (Nat.lt_succ_self n) init where
  /--
  Inner loop for `Fin.dfoldrM`.
  ```
  Fin.dfoldrM.loop n f i h xᵢ = do
    let xᵢ₋₁ ← f (i-1) xᵢ
    ...
    let x₁ ← f 1 x₂
    let x₀ ← f 0 x₁
    pure x₀
  ```
  -/
  @[specialize] loop (i : Nat) (h : i < n + 1) (x : α ⟨i, h⟩) : m (α 0) :=
    match i with
    | i + 1 => (f ⟨i, Nat.lt_of_succ_lt_succ h⟩ x) >>= loop i (Nat.lt_of_succ_lt h)
    | 0 => pure x

/-- Heterogeneous fold over `Fin n` from the right: `foldr 3 f x = f 0 (f 1 (f 2 x))`, where
`f 2 : α 3 → α 2`, `f 1 : α 2 → α 1`, etc.

This is the dependent version of `Fin.foldr`. -/
@[inline] def dfoldr (n : Nat) (α : Fin (n + 1) → Type _)
    (f : ∀ (i : Fin n), α i.succ → α i.castSucc) (init : α (last n)) : α 0 :=
  dfoldrM (m := Id) n α f init

/-- Heterogeneous monadic fold over `Fin n` from left to right:
```
Fin.foldlM n f x₀ = do
  let x₁ : α 1 ← f 0 x₀
  let x₂ : α 2 ← f 1 x₁
  ...
  let xₙ : α n ← f (n-1) xₙ₋₁
  pure xₙ
```
This is the dependent version of `Fin.foldlM`. -/
@[inline] def dfoldlM [Monad m] (n : Nat) (α : Fin (n + 1) → Type _)
    (f : ∀ (i : Fin n), α i.castSucc → m (α i.succ)) (init : α 0) : m (α (last n)) :=
  loop 0 (Nat.zero_lt_succ n) init where
  /-- Inner loop for `Fin.dfoldlM`.
    ```
  Fin.foldM.loop n α f i h xᵢ = do
    let xᵢ₊₁ : α (i+1) ← f i xᵢ
    ...
    let xₙ : α n ← f (n-1) xₙ₋₁
    pure xₙ
  ```
  -/
  @[semireducible, specialize] loop (i : Nat) (h : i < n + 1) (x : α ⟨i, h⟩) : m (α (last n)) :=
    if h' : i < n then
      (f ⟨i, h'⟩ x) >>= loop (i + 1) (Nat.succ_lt_succ h')
    else
      haveI : ⟨i, h⟩ = last n := by ext; simp; omega
      _root_.cast (congrArg (fun i => m (α i)) this) (pure x)

/-- Heterogeneous fold over `Fin n` from the left: `foldl 3 f x = f 0 (f 1 (f 2 x))`, where
`f 0 : α 0 → α 1`, `f 1 : α 1 → α 2`, etc.

This is the dependent version of `Fin.foldl`. -/
@[inline] def dfoldl (n : Nat) (α : Fin (n + 1) → Type _)
    (f : ∀ (i : Fin n), α i.castSucc → α i.succ) (init : α 0) : α (last n) :=
  dfoldlM (m := Id) n α f init

/--
`findSome? f` returns `f i` for the first `i` for which `f i` is `some _`, or `none` if no such
element is found. The function `f` is not evaluated on further inputs after the first `i` is found.
-/
@[inline] def findSome? (f : Fin n → Option α) : Option α :=
  foldl n (fun r i => r <|> f i) none

/--
`find? p` returns the first `i` for which `p i = true`, or `none` if no such element is found.
The function `p` is not evaluated on further inputs after the first `i` is found.
-/
@[inline] def find? (p : Fin n → Bool) : Option (Fin n) :=
  findSome? <| Option.guard fun i => p i
