import Batteries.Data.String.AsciiCasing
import Batteries.Data.String.CaseInsensitiveAsciiOnly

#guard "ABC".caseFoldAsciiOnly == "abc"
#guard "x".caseFoldAsciiOnly != "y"
#guard "Àà".caseFoldAsciiOnly == "Àà"
#guard "1$#!".caseFoldAsciiOnly == "1$#!"

#guard "abc".beqCaseInsensitiveAsciiOnly "ABC" == true
#guard "cba".beqCaseInsensitiveAsciiOnly "ABC" == false
#guard "a".beqCaseInsensitiveAsciiOnly "a" == true
#guard "$".beqCaseInsensitiveAsciiOnly "$" == true
#guard "a".beqCaseInsensitiveAsciiOnly "b" == false
#guard "γ".beqCaseInsensitiveAsciiOnly "Γ" == false
#guard "ä".beqCaseInsensitiveAsciiOnly "Ä" == false

#guard  "abc".cmpCaseInsensitiveAsciiOnly "ABC" == .eq
#guard  "abc".cmpCaseInsensitiveAsciiOnly "xyz" == .lt
#guard  "a".cmpCaseInsensitiveAsciiOnly "a" == .eq
#guard  "$".cmpCaseInsensitiveAsciiOnly "$" == .eq
#guard  "a__".cmpCaseInsensitiveAsciiOnly "b__" == .lt
#guard  "γ".cmpCaseInsensitiveAsciiOnly "Γ" == .gt
#guard  "ä".cmpCaseInsensitiveAsciiOnly "Ä" == .gt

open String.CaseInsensitiveAsciiOnly (ofString)

#guard ofString "abc" == ofString "ABC"
#guard ofString "a" != ofString "b"

#guard [
  (ofString "", ofString ""),
  (ofString "  ", ofString "  "),
  (ofString "a", ofString "A"),
  (ofString "abc", ofString "ABC"),
  (ofString "aBc", ofString "AbC"),
  (ofString "123", ofString "123"),
  (ofString "国际化与本地化", ofString "国际化与本地化"),
  (ofString "ABC😂🔰🍑xyz", ofString "abc😂🔰🍑XYZ")
].all (fun (a, b) => a = b && a.toLowerString = b.toLowerString)

#guard [
  (ofString "国际化", ofString "国际化与本地化"),
  (ofString "", ofString " "),
  (ofString "a", ofString "b"),
  (ofString "ab", ofString "ba"),
  (ofString "123", ofString "124"),
  (ofString "😂", ofString "🍑"),
  (ofString "🔰🍑", ofString "😂🔰🍑aaa")
].all (fun (a, b) => a ≠ b && a.toLowerString != b.toLowerString)
