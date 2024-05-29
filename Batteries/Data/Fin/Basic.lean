/-
Copyright (c) 2017 Robert Y. Lewis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Y. Lewis, Keeley Hoek, Mario Carneiro
-/

namespace Fin

/-- `min n m` as an element of `Fin (m + 1)` -/
def clamp (n m : Nat) : Fin (m + 1) := ⟨min n m, Nat.lt_succ_of_le (Nat.min_le_right ..)⟩

/-- `enum n` is the array of all elements of `Fin n` in order -/
def enum (n) : Array (Fin n) := Array.ofFn id

/-- `list n` is the list of all elements of `Fin n` in order -/
def list (n) : List (Fin n) := (enum n).data

/--
Folds a monadic function over `Fin n` from left to right:
```
Fin.foldlM n f x₀ = do
  let x₁ ← f x₀ 0
  let x₂ ← f x₁ 1
  ...
  let xₙ ← f xₙ₋₁ (n-1)
  pure xₙ
```
-/
@[inline] def foldlM [Monad m] (n) (f : α → Fin n → m α) (init : α) : m α := loop init 0 where
  /--
  Inner loop for `Fin.foldlM`.
  ```
  Fin.foldlM.loop n f xᵢ i = do
    let xᵢ₊₁ ← f xᵢ i
    ...
    let xₙ ← f xₙ₋₁ (n-1)
    pure xₙ
  ```
  `Fin.foldlM.loop n f x i = f x i >>= fun x => f x (i+1) >>= ...`
  -/
  loop (x : α) (i : Nat) : m α := do
    if h : i < n then f x ⟨i, h⟩ >>= (loop · (i+1)) else pure x
  termination_by n - i

/--
Folds a monadic function over `Fin n` from right to left:
```
Fin.foldrM n f x₀ = do
  let x₁ ← f (n-1) x₀
  let x₂ ← f (n-2) x₁
  ...
  let xₙ ← f 0 xₙ₋₁
  pure xₙ
```
-/
@[inline] def foldrM [Monad m] (n) (f : Fin n → α → m α) (init : α) : m α :=
  loop ⟨n, Nat.le_refl n⟩ init where
  /--
  Inner loop for `Fin.foldrM`.
  ```
  Fin.foldrM n f i x₀ = do
    let x₁ ← f (n-1) x₀
    let x₂ ← f (n-2) x₁
    ...
    let xᵢ ← f (n-i) xᵢ₋₁
    pure xᵢ
  ```
  -/
  loop : {i // i ≤ n} → α → m α
  | ⟨0, _⟩, x => pure x
  | ⟨i+1, h⟩, x => f ⟨i, h⟩ x >>= loop ⟨i, Nat.le_of_lt h⟩

-- These are also defined in core in the root namespace!

/-- Folds over `Fin n` from the right: `foldr 3 f x = f 0 (f 1 (f 2 x))`. -/
@[inline] def foldr (n) (f : Fin n → α → α) (init : α) : α :=
  foldrM (m:=Id) n f init

/-- Folds over `Fin n` from the left: `foldl 3 f x = f (f (f x 0) 1) 2`. -/
@[inline] def foldl (n) (f : α → Fin n → α) (init : α) : α :=
  foldlM (m:=Id) n f init
