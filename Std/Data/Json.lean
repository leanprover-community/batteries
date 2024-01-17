/-
 Copyright (c) 2022 E.W.Ayers. All rights reserved.
 Released under Apache 2.0 license as described in the file LICENSE.
 Authors: E.W.Ayers, Wojciech Nawrocki
-/
import Lean.Data.Json.FromToJson
import Lean.Syntax

/-!
# JSON-like syntax for Lean.

Now you can write

```lean
open Std.Json

#eval json% {
  hello : "world",
  cheese : ["edam", "cheddar", {kind : "spicy", rank : 100.2}],
  lemonCount : 100e30,
  isCool : true,
  isBug : null,
  lookACalc: $(23 + 54 * 2)
}
```
-/

namespace Std.Json
open Lean

/-- Json syntactic category -/
declare_syntax_cat jso (behavior := symbol)
/-- Json null value syntax. -/
syntax "null" : jso
/-- Json true value syntax. -/
syntax "true" : jso
/-- Json false value syntax. -/
syntax "false" : jso
/-- Json string syntax. -/
syntax str : jso
/-- Json number negation syntax for ordinary numbers. -/
syntax "-"? num : jso
/-- Json number negation syntax for scientific numbers. -/
syntax "-"? scientific : jso
/-- Json array syntax. -/
syntax "[" jso,* "]" : jso
/-- Json identifier syntax. -/
syntax jsoIdent := ident <|> str
/-- Json key/value syntax. -/
syntax jsoField := jsoIdent ": " jso
/-- Json object syntax. -/
syntax "{" jsoField,* "}" : jso
/-- Allows to use Json syntax in a Lean file. -/
syntax "json% " jso  : term


macro_rules
  | `(json% null)           => `(Lean.Json.null)
  | `(json% true)           => `(Lean.Json.bool Bool.true)
  | `(json% false)          => `(Lean.Json.bool Bool.false)
  | `(json% $n:str)         => `(Lean.Json.str $n)
  | `(json% $n:num)         => `(Lean.Json.num $n)
  | `(json% $n:scientific)  => `(Lean.Json.num $n)
  | `(json% -$n:num)        => `(Lean.Json.num (-$n))
  | `(json% -$n:scientific) => `(Lean.Json.num (-$n))
  | `(json% [$[$xs],*])     => `(Lean.Json.arr #[$[json% $xs],*])
  | `(json% {$[$ks:jsoIdent : $vs:jso],*}) => do
    let ks : Array (TSyntax `term) ← ks.mapM fun
      | `(jsoIdent| $k:ident) => pure (k.getId |> toString |> quote)
      | `(jsoIdent| $k:str)   => pure k
      | _                     => Macro.throwUnsupported
    `(Lean.Json.mkObj [$[($ks, json% $vs)],*])
  | `(json% $stx)           =>
    if stx.raw.isAntiquot then
      let stx := ⟨stx.raw.getAntiquotTerm⟩
      `(Lean.toJson $stx)
    else
      Macro.throwUnsupported

end Std.Json
