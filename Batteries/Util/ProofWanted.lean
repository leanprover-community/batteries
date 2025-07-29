/-
Copyright (c) 2023 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Thrane Christiansen
-/
import Lean.Elab.Exception
import Lean.Elab.Command


open Lean Parser Elab Command

/-- This proof would be a welcome contribution to the library!

The syntax of `proof_wanted` (or `open_problem`) declarations is just like that of `theorem`, but
without `:=` or the proof. Lean checks that these declarations are well-formed (e.g. it ensures that
all the mentioned names are in scope, and that the theorem statement is a valid proposition), but
they are discarded afterwards. This means that they cannot be used as axioms.

The `open_problem` syntax variant exists to be able to distinguish between theorems and conjectures,
i.e. between statements we (informally) know to be true but haven't proven in Lean yet, and
statements for which we don't (informally) know if they are true. There is no difference to Lean in
semantics.

Typical usage:
```
@[simp] proof_wanted empty_find? [BEq α] [Hashable α] {a : α} :
    (∅ : HashMap α β).find? a = none
```
-/
@[command_parser]
def «proof_wanted» := leading_parser
  declModifiers false >> ("proof_wanted" <|> "open_problem") >> declId >> ppIndent declSig

/-- Elaborate a `proof_wanted` declaration. The declaration is translated to an axiom during
elaboration, but it's then removed from the environment.
-/
@[command_elab «proof_wanted»]
def elabProofWanted : CommandElab
  /- We don't need another branch for the `open_problem` variant, as lean (as of 4.22.0-rc4) doesn't
    check token atoms match when matching with syntax quotations. -/
  | `($mods:declModifiers proof_wanted $name $args* : $res) => withoutModifyingEnv do
    -- The helper axiom is used instead of `sorry` to avoid spurious warnings
    elabCommand <| ← `(
      section
      set_option linter.unusedVariables false
      axiom helper {α : Sort _} : α
      $mods:declModifiers theorem $name $args* : $res := helper
      end)
  | _ => throwUnsupportedSyntax
