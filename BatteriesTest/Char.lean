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
