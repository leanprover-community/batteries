import Batteries.Data.Char
import Batteries.Data.Char.AsciiCasing

namespace String

/-- Case folding for ASCII characters only.

Alphabetic ASCII characters are mapped to their lowercase form, all other characters are left
unchanged. This agrees with the Unicode case folding algorithm for ASCII characters.

```
#eval "ABC".caseFoldAsciiOnly == "abc" -- true
#eval "x".caseFoldAsciiOnly == "y" -- false
#eval "Àà".caseFoldAsciiOnly == "Àà" -- true
#eval "1$#!".caseFoldAsciiOnly == "1$#!" -- true
```
-/
abbrev caseFoldAsciiOnly (s : String) := s.map Char.caseFoldAsciiOnly

/--
Bool-valued comparison of two `String`s for *ASCII*-case insensitive equality.
-/
def beqCaseInsensitiveAsciiOnly (s₁ s₂ : String) : Bool :=
  s₁.caseFoldAsciiOnly == s₂.caseFoldAsciiOnly

theorem beqCaseInsensitiveAsciiOnly.eqv : Equivalence (beqCaseInsensitiveAsciiOnly · ·) := {
  refl _ := BEq.rfl
  trans := fun h1 h2 => by simp_all [beqCaseInsensitiveAsciiOnly]
  symm := by simp_all [beqCaseInsensitiveAsciiOnly]
}

/--
Setoid structure on `String` usig `beqCaseInsensitiveAsciiOnly`
-/
def beqCaseInsensitiveAsciiOnly.isSetoid : Setoid String :=
  ⟨(beqCaseInsensitiveAsciiOnly · ·), beqCaseInsensitiveAsciiOnly.eqv⟩

/--
ASCII-case insensitive implementation comparison returning an `Ordering`. Useful for sorting.

```
#eval cmpCaseInsensitiveAsciiOnly "a" "A" -- eq
#eval cmpCaseInsensitiveAsciiOnly "a" "a" -- eq
#eval cmpCaseInsensitiveAsciiOnly "$" "$" -- eq
#eval cmpCaseInsensitiveAsciiOnly "a" "b" -- lt
#eval cmpCaseInsensitiveAsciiOnly "γ" "Γ" -- gt
#eval cmpCaseInsensitiveAsciiOnly "ä" "Ä" -- gt
```
-/
def cmpCaseInsensitiveAsciiOnly (s₁ s₂ : String) : Ordering :=
  compare s₁.caseFoldAsciiOnly s₂.caseFoldAsciiOnly
