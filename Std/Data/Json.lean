/-
 Copyright (c) 2022 E.W.Ayers. All rights reserved.
 Released under Apache 2.0 license as described in the file LICENSE.
 Authors: E.W.Ayers
-/
import Lean.Data.Json

/-!
# JSON-like syntax for Lean.

Now you can write

```lean
open scoped ProofWidgets.Json

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

namespace ProofWidgets.Json
open Lean

/-- Json data syntax. -/
declare_syntax_cat jso (behavior := symbol)
/-- Json data field syntax. -/
declare_syntax_cat jso_field
/-- Json identifier syntax. -/
declare_syntax_cat jso_ident

instance : OfScientific JsonNumber where
  ofScientific mantissa exponentSign decimalExponent :=
    if exponentSign then
      {mantissa := mantissa, exponent := decimalExponent}
    else
      {mantissa := (mantissa * 10 ^ decimalExponent : Nat), exponent := 0}

instance : Neg JsonNumber where
  neg jn := ⟨- jn.mantissa, jn.exponent⟩

instance : ToJson Float where
  toJson x :=
    if x == 0.0 then 0 else
    let s := toString (if x < 0.0 then - x else x)
    match Lean.Syntax.decodeScientificLitVal? <| s with
    | none =>
      match s with
      | "inf" => "inf" -- [todo] emit a warning
      | "-inf" => "-inf"
      | "nan" => "nan"
      | _ => panic! s!"unhandled float string {s}"
    | some (m, e, de) =>
      let j : JsonNumber := OfScientific.ofScientific m e de
      let j := if x < 0.0 then -j else j
      Json.num j

/-- Json array syntax. -/
scoped syntax "[" jso,* "]" : jso
/-- Json number negation syntax for scientific numbers. -/
scoped syntax "-"? scientific : jso
/-- Json number negation syntax for ordinary numbers. -/
scoped syntax "-"? num : jso
/-- Json string syntax. -/
scoped syntax str : jso
/-- Json true value syntax. -/
scoped syntax "true" : jso
/-- Json false value syntax. -/
scoped syntax "false" : jso
/-- Json null value syntax. -/
scoped syntax "null" : jso
/-- Json identifier syntax. -/
scoped syntax ident : jso_ident
/-- Json quotation syntax for keys. -/
scoped syntax "$(" term ")" : jso_ident
/-- Json string key syntax. -/
scoped syntax str : jso_ident
/-- Json key/value syntax. -/
scoped syntax jso_ident ": " jso : jso_field
/-- Json dictionary syntax. -/
scoped syntax "{" jso_field,* "}" : jso
/-- Json quotation syntax for values. -/
scoped syntax "$(" term ")" : jso
/-- Allows to use Json syntax in a Lean file. -/
scoped syntax "json% " jso  : term

macro_rules
  | `(json% $($t))          => `(Lean.toJson $t)
  | `(json% null)           => `(Lean.Json.null)
  | `(json% true)           => `(Lean.Json.bool Bool.true)
  | `(json% false)          => `(Lean.Json.bool Bool.false)
  | `(json% $n:str)         => `(Lean.Json.str $n)
  | `(json% $n:num)         => `(Lean.Json.num $n)
  | `(json% $n:scientific)  => `(Lean.Json.num $n)
  | `(json% -$n:num)        => `(Lean.Json.num (-$n))
  | `(json% -$n:scientific) => `(Lean.Json.num (-$n))
  | `(json% [$[$xs],*])     => `(Lean.Json.arr #[$[json% $xs],*])
  | `(json% {$[$ks:jso_ident : $vs:jso],*}) =>
    let ks : Array (TSyntax `term) := ks.map fun
      | `(jso_ident| $k:ident)   => (k.getId |> toString |> quote)
      | `(jso_ident| $k:str)     => k
      | `(jso_ident| $($k:term)) => k
      | stx                      => panic! s!"unrecognized ident syntax {stx}"
    `(Lean.Json.mkObj [$[($ks, json% $vs)],*])

end ProofWidgets.Json
