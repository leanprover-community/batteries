/-
Copyright (c) 2025 Christopher Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Bailey, F. G. Dorais
-/
module

public import Batteries.Data.Char
public import Batteries.Data.Char.AsciiCasing

@[expose] public section

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

-- TODO: Reimplement with finite iterators/streams when available for `String`.
private partial def beqCaseInsensitiveAsciiOnlyImpl (s₁ s₂ : String) : Bool :=
  s₁.length == s₂.length && loop (ToStream.toStream s₁) (ToStream.toStream s₂)
where
  loop i₁ i₂ := match Stream.next? i₁, Stream.next? i₂ with
    | some (c₁, i₁), some (c₂, i₂) => c₁.beqCaseInsensitiveAsciiOnly c₂ && loop i₁ i₂
    | none, none => true
    | _, _ => false

/--
Bool-valued comparison of two `String`s for *ASCII*-case insensitive equality.

#eval "abc".beqCaseInsensitiveAsciiOnly "ABC" -- true
#eval "cba".beqCaseInsensitiveAsciiOnly "ABC" -- false
#eval "$".beqCaseInsensitiveAsciiOnly "$" -- true
#eval "a".beqCaseInsensitiveAsciiOnly "b" -- false
#eval "γ".beqCaseInsensitiveAsciiOnly "Γ" -- false
-/
@[implemented_by beqCaseInsensitiveAsciiOnlyImpl]
def beqCaseInsensitiveAsciiOnly (s₁ s₂ : String) : Bool :=
  s₁.caseFoldAsciiOnly == s₂.caseFoldAsciiOnly

theorem beqCaseInsensitiveAsciiOnly.eqv : Equivalence (beqCaseInsensitiveAsciiOnly · ·) := {
  refl _ := BEq.rfl
  trans _ _ := by simp_all [beqCaseInsensitiveAsciiOnly]
  symm := by simp_all [beqCaseInsensitiveAsciiOnly]
}

/--
Setoid structure on `String` usig `beqCaseInsensitiveAsciiOnly`
-/
def beqCaseInsensitiveAsciiOnly.isSetoid : Setoid String :=
  ⟨(beqCaseInsensitiveAsciiOnly · ·), beqCaseInsensitiveAsciiOnly.eqv⟩

-- TODO: Reimplement with finite iterators/streams when available for `String`.
private partial def cmpCaseInsensitiveAsciiOnlyImpl (s₁ s₂ : String) : Ordering :=
  loop (ToStream.toStream s₁) (ToStream.toStream s₂)
where
  loop i₁ i₂ := match Stream.next? i₁, Stream.next? i₂ with
    | some (c₁, i₁), some (c₂, i₂) => c₁.cmpCaseInsensitiveAsciiOnly c₂ |>.then (loop i₁ i₂)
    | some _, none => .gt
    | none, some _ => .lt
    | none, none => .eq

/--
ASCII-case insensitive implementation comparison returning an `Ordering`. Useful for sorting.

```
#eval cmpCaseInsensitiveAsciiOnly "a" "A" -- eq
#eval cmpCaseInsensitiveAsciiOnly "a" "a" -- eq
#eval cmpCaseInsensitiveAsciiOnly "$" "$" -- eq
#eval cmpCaseInsensitiveAsciiOnly "a" "b" -- lt
#eval cmpCaseInsensitiveAsciiOnly "γ" "Γ" -- gt
```
-/
@[implemented_by cmpCaseInsensitiveAsciiOnlyImpl]
def cmpCaseInsensitiveAsciiOnly (s₁ s₂ : String) : Ordering :=
  compare s₁.caseFoldAsciiOnly s₂.caseFoldAsciiOnly
