/-
Copyright (c) 2024 François G. Dorais. All rights reserved.
Released under Apache 2. license as described in the file LICENSE.
Authors: François G. Dorais
-/

/-- Drop up to `n` values from the stream `s`. -/
def Stream.drop [Stream σ α] (s : σ) : Nat → σ
  | 0 => s
  | n+1 => match Stream.next? s with
    | none => s
    | some (_, s) => drop s n

/-- Read up to `n` values from the stream `s`. -/
def Stream.take [Stream σ α] (s : σ) (n : Nat) : Array α × σ :=
  loop s (.mkEmpty n) n
where
  /-- Inner loop for `Stream.take`. -/
  loop (s : σ) (acc : Array α)
    | 0 => (acc, s)
    | n+1 => match Stream.next? s with
      | none => (acc, s)
      | some (v, s) => loop s (acc.push v) n
