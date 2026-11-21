/-
Copyright (c) 2022 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
module

public import Batteries.Data.Float.Basic

/-! Non-public helpers, mostly for parsing `Rat`s -/

section ParserHelpers

/--
  A monad suitable for parsing parts of strings
-/
abbrev ParserM := StateT String.Slice Option

/--
  Attempts to extract the given `c`
  On success, returns `true` and removes `c` from the beginning of the state string
  On non-success, returns `false`
-/
def dropChar (c : Char) : ParserM Bool := do
  match (← get).dropPrefix? c with
  | none => return false
  | some s => set s; return true

/--
  Splits the given `str` into two pieces
  `.1` all of the beginning characters that consecutively match the given `pat`
  `.2` the rest of the string
-/
def splitWhile {ρ : Type} (str : String.Slice) (pat : ρ)
              [String.Slice.Pattern.ForwardPattern pat]
: String.Slice × String.Slice
:=
  let pos := str.skipPrefixWhile pat
  ⟨ str.sliceTo pos, str.sliceFrom pos ⟩

/--
  Extracts the sign (+-) from the beginning of the state.
  Returns `1` or `-1`.
  Defaults to `1`.
-/
def extractSignD : ParserM Int := do
  if      ← dropChar '+' then return  1
  else if ← dropChar '-' then return -1
  return 1

/--
  Extracts a number from the beginning of the state.
  Returns
  `.1` The natural number
  `.2` The number of digits extracted
-/
def extractNat : ParserM (Nat × Nat) := do
  let (baseStr, leftover) := splitWhile (← get) Char.isDigit
  set leftover
  match baseStr.toNat? with
  | .none => failure
  -- The following assumes that `Char.isDigit` only matches 1-byte characters
  | .some n => return (n, baseStr.utf8ByteSize)

/--
  Shorthand that only extracts a natural number
-/
def extractNat' : ParserM Nat := do
  pure (← extractNat).1

end ParserHelpers

public section

/-! # Rational Numbers and Float -/

namespace Rat

/--
  Tries to parse a decimal string into a `Rat`
  A decimal string is of the form
  ```
  ["+" | "-"]
  Nat
  [".", Nat]
  ["e", Nat]
  ```

  On parsing failure, returns `none`
-/
def ofDecimalString? (str : String.Slice) : Option Rat :=
  StateT.run' (s := str) do
    let sign ← extractSignD
    let (base, baseDigits) ← extractNat <|> pure (0, 0)
    let mut base := base
    let mut div₁₀ := 0

    if ← dropChar '.' then
      let (dec, decDigits) ← extractNat <|> pure (0, 0)
      guard ((baseDigits != 0) || (decDigits != 0))
      base := (base * 10 ^ decDigits) + dec
      div₁₀ := div₁₀ + decDigits
    else if baseDigits == 0 then failure

    if ← dropChar 'e' then
      let expSign ← extractSignD
      let (val, _) ← extractNat
      if expSign > 0 then base := base * (10 ^ val)
      else             div₁₀ := div₁₀ + val

    guard (← get).isEmpty
    return mkRat (sign * base) (10 ^ div₁₀)

/--
  Tries to parse a fraction string into a `Rat`
  A fraction string is of the form

  ```
  ["+" | "-"]
  Nat
  ["/", Nat]
  ```
-/
def ofFractionString? (str : String.Slice) : Option Rat :=
  StateT.run' (s := str) do
    let sign ← extractSignD
    let numerator ← extractNat'

    let denominator ← do
      if ← dropChar '/' then extractNat'
      else pure 1

    guard (denominator != 0)
    guard (← get).isEmpty
    return mkRat (numerator * sign) denominator

/--
  Returns a string in the form of
  ```
  ["-"]
  Nat
  ["/", Nat]
  ```

  This function should be an identity:
  `ofFractionString? toFractionString`
-/
def toFractionString (r : Rat) : String :=
  match r.den with
  | 1 => r.num.repr
  | d => r.num.repr ++ "/" ++ d.repr

/-- Convert this rational number to a `Float` value. -/
protected def toFloat (a : Rat) : Float := a.num.divFloat a.den

/-- Convert this floating point number to a rational value. -/
protected def _root_.Float.toRat? (a : Float) : Option Rat :=
  a.toRatParts.map fun (v, exp) =>
    mkRat (v.sign * v.natAbs <<< exp.toNat) (1 <<< (-exp).toNat)

/--
Convert this floating point number to a rational value,
mapping non-finite values (`inf`, `-inf`, `nan`) to 0.
-/
protected def _root_.Float.toRat0 (a : Float) : Rat := a.toRat?.getD 0

instance : Coe Rat Float := ⟨Rat.toFloat⟩

end Rat
