/-
Copyright (c) 2023 Christopher Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Bailey
-/
import Batteries.Data.Char
import Batteries.Data.String.Basic
import Batteries.Data.String.Lemmas

/-! # Ascii-case insensitive Strings

UTF-8 strings with ascii-case insensitive equality.
-/


/--
A UTF-8 string which is *ascii*-case-insensitive. Useful in contexts like networking.
-/
@[reducible]
def StringInsensitiveAsciiCase := Quotient ⟨_, String.eqIgnoreAsciiCase.eqv⟩

namespace StringInsensitiveAsciiCase

instance instDecidableEq : DecidableEq StringInsensitiveAsciiCase :=
  fun x y =>
    Quotient.recOnSubsingleton₂ x y
      fun a₁ a₂ =>
        if h: a₁.toLower = a₂.toLower
        then isTrue (Quotient.sound h)
        else isFalse fun hf => absurd (Quotient.exact hf) h

/--
Constructor for `StringInsensitiveAsciiCase` (since the type is implemented as a Quotient)
-/
def ofString : String → StringInsensitiveAsciiCase := Quot.mk _

instance instInhabited : Inhabited StringInsensitiveAsciiCase := ⟨ofString ""⟩

/--
Returns the length of an ascii-case insensitive string in Unicode code points using `String.length`
-/
def length : StringInsensitiveAsciiCase → Nat :=
  Quot.lift String.length (fun _ _ => String.length_eq_of_map_eq)

/--
Get the underlying value by extracting as a lower-case `String`
-/
def toLowerString : StringInsensitiveAsciiCase → String :=
  Quot.lift String.toLower (fun _ _ => by simp [String.eqIgnoreAsciiCase])

/--
Hash a `StringInsensitiveAsciiCase` using the ascii-lowercase representation of the string.
-/
def hash : StringInsensitiveAsciiCase → UInt64 :=
  Quot.lift (·.toLower.hash) (fun _ _ => by simp [String.eqIgnoreAsciiCase]; intro _; simp only [*])

instance instHashable : Hashable StringInsensitiveAsciiCase := ⟨hash⟩

instance instToString : ToString StringInsensitiveAsciiCase := ⟨toLowerString⟩

instance instRepr : Repr StringInsensitiveAsciiCase where
  reprPrec s _ := repr s.toLowerString
