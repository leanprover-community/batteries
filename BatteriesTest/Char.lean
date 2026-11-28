import Batteries.Data.Char

/- Failing on nightly-2025-12-18
#guard Char.caseFoldAsciiOnly 'A' == 'a'
#guard Char.caseFoldAsciiOnly 'a' == 'a'
#guard Char.caseFoldAsciiOnly 'À' == 'À'
#guard Char.caseFoldAsciiOnly 'à' == 'à'
#guard Char.caseFoldAsciiOnly '$' == '$'

#guard Char.beqCaseInsensitiveAsciiOnly 'a' 'A' == true
#guard Char.beqCaseInsensitiveAsciiOnly 'a' 'a' == true
#guard Char.beqCaseInsensitiveAsciiOnly '$' '$' == true
#guard Char.beqCaseInsensitiveAsciiOnly 'a' 'b' == false
#guard Char.beqCaseInsensitiveAsciiOnly 'γ' 'Γ' == false
#guard Char.beqCaseInsensitiveAsciiOnly 'ä' 'Ä' == false

#guard Char.cmpCaseInsensitiveAsciiOnly 'a' 'A' == .eq
#guard Char.cmpCaseInsensitiveAsciiOnly 'a' 'a' == .eq
#guard Char.cmpCaseInsensitiveAsciiOnly '$' '$' == .eq
#guard Char.cmpCaseInsensitiveAsciiOnly 'a' 'b' == .lt
#guard Char.cmpCaseInsensitiveAsciiOnly 'γ' 'Γ' == .gt
#guard Char.cmpCaseInsensitiveAsciiOnly 'ä' 'Ä' == .gt
-/

/-! Bounded quantifiers over `Char` are decided by checking only the code points below the bound. -/

example : ∀ c : Char, c.val < 0x80 → c.isUpper → c.isAlpha := by decide
example : ∀ c : Char, c.toNat < 128 → c.isDigit → c.isAlphanum := by decide
example : ¬ ∃ c : Char, c.toNat < 0x41 ∧ c.isUpper := by decide
example : ∃ c : Char, c.val < 0x80 ∧ c.isWhitespace := by decide +kernel
example : ∀ c : Char, c.toNat < 0x100 → c.toNat < 0x80 ∨ ¬ c.isAlpha := by decide +kernel
