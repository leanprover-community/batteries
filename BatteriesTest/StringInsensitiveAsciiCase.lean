import Batteries.Data.StringInsensitiveAsciiCase

open StringInsensitiveAsciiCase (ofString)

/-- info: true -/
#guard_msgs in
#eval [
  (ofString "", ofString ""),
  (ofString "  ", ofString "  "),
  (ofString "a", ofString "A"),
  (ofString "abc", ofString "ABC"),
  (ofString "aBc", ofString "AbC"),
  (ofString "123", ofString "123"),
  (ofString "国际化与本地化", ofString "国际化与本地化"),
  (ofString "ABC😂🔰🍑xyz", ofString "abc😂🔰🍑XYZ")
].all (fun (a, b) => a = b && a.toLowerString = b.toLowerString)

/-- info: true -/
#guard_msgs in #eval [
  (ofString "国际化", ofString "国际化与本地化"),
  (ofString "", ofString " "),
  (ofString "a", ofString "b"),
  (ofString "ab", ofString "ba"),
  (ofString "123", ofString "124"),
  (ofString "😂", ofString "🍑"),
  (ofString "🔰🍑", ofString "😂🔰🍑aaa")
].all (fun (a, b) => a ≠ b && a.toLowerString != b.toLowerString)
