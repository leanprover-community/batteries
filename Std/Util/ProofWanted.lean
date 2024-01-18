/-
Copyright (c) 2023 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Thrane Christiansen
-/
import Lean.Elab.Exception
import Lean.Elab.Command


open Lean Parser Elab Command

/-- This proof would be a welcome contribution to the library!

The syntax of `proof_wanted` declarations is just like that of `theorem`, but without `:=` or the
proof. Lean checks that `proof_wanted` declarations are well-formed (e.g. it ensures that all the
mentioned names are in scope, and that the theorem statement is a valid proposition), but they are
discarded afterwards. This means that they cannot be used as axioms.

Typical usage:
```
@[simp] proof_wanted empty_find? [BEq α] [Hashable α] {a : α} :
    (∅ : HashMap α β).find? a = none
```
-/
@[command_parser]
def «proof_wanted» := leading_parser
  declModifiers false >> "proof_wanted" >> declId >> ppIndent declSig

/-- Elaborate a `proof_wanted` declaration. The declaration is translated to an axiom during
elaboration, but it's then removed from the environment.
-/
@[command_elab «proof_wanted»]
def elabProofWanted : CommandElab
  | `($mods:declModifiers proof_wanted $name $args* : $res) => withoutModifyingEnv do
    -- The helper axiom is used instead of `sorry` to avoid spurious warnings
    elabCommand <| ← `(axiom helper (p : Prop) : p
                       $mods:declModifiers
                       theorem $name $args* : $res := helper _)
  | _ => throwUnsupportedSyntax
