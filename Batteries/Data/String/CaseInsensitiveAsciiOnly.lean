/-
Copyright (c) 2023 Christopher Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Bailey
-/
import Batteries.Data.Char
import Batteries.Data.String.Basic
import Batteries.Data.String.Lemmas
import Batteries.Data.String.AsciiCasing

namespace String

/-! # Ascii-case insensitive Strings

UTF-8 strings with ASCII-case insensitive equality.
-/

/--
A UTF-8 string which is *ASCII*-case-insensitive. Useful in contexts like networking.
-/
@[reducible]
def CaseInsensitiveAsciiOnly := Quotient ⟨_, String.beqCaseInsensitiveAsciiOnly.eqv⟩

namespace CaseInsensitiveAsciiOnly

instance instDecidableEq : DecidableEq CaseInsensitiveAsciiOnly :=
  fun x y =>
    Quotient.recOnSubsingleton₂ x y
      fun a₁ a₂ =>
        if h: a₁.caseFoldAsciiOnly == a₂.caseFoldAsciiOnly
        then isTrue (Quotient.sound h)
        else isFalse fun hf => absurd (Quotient.exact hf) h

/--
Constructor for `CaseInsensitiveAsciiOnly` (since the type is implemented as a Quotient)
-/
def ofString : String → CaseInsensitiveAsciiOnly := Quot.mk _

instance instInhabited : Inhabited CaseInsensitiveAsciiOnly := ⟨ofString ""⟩

/--
Returns the length of an ASCII-case insensitive string in Unicode code points using `String.length`
-/
def length : CaseInsensitiveAsciiOnly → Nat :=
  Quot.lift String.length fun a b => by
    simp only [String.beqCaseInsensitiveAsciiOnly, beq_iff_eq]
    apply String.length_eq_of_map_eq

/--
Get the underlying value by extracting as a lower-case `String`
-/
def toLowerString : CaseInsensitiveAsciiOnly → String :=
  Quot.lift String.caseFoldAsciiOnly
    fun _ _ => by simp [String.beqCaseInsensitiveAsciiOnly]

/--
Hash a `CaseInsensitiveAsciiOnly` using the ASCII-lowercase representation of the string.
-/
def hash : CaseInsensitiveAsciiOnly → UInt64 :=
  Quot.lift (·.caseFoldAsciiOnly.hash)
    fun _ _ => by simp [String.beqCaseInsensitiveAsciiOnly]; intro _; simp only [*]

instance instHashable : Hashable CaseInsensitiveAsciiOnly := ⟨hash⟩

instance instToString : ToString CaseInsensitiveAsciiOnly := ⟨toLowerString⟩

instance instRepr : Repr CaseInsensitiveAsciiOnly where
  reprPrec s _ := repr s.toLowerString
