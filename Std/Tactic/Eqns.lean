/-
Copyright (c) 2023 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
import Lean.Meta.Eqns
import Lean.Elab.InfoTree.Main
import Lean.Elab.Exception
import Std.Lean.NameMapAttribute

/-! # The `@[eqns]` attribute

This file provides the `eqns` attribute as a way of overriding the default equation lemmas.
-/
open Lean Elab

namespace Std.Tactic

/--
Overrides the default equation lemmas. For example

```
def transpose {m n} (A : m → n → Nat) : n → m → Nat
  | i, j => A j i

theorem transpose_apply {m n} (A : m → n → Nat) (i j) :
  transpose A i j = A j i := rfl

attribute [eqns transpose_apply] transpose

theorem transpose_const {m n} (c : Nat) :
    transpose (fun (i : m) (j : n) => c) = fun j i => c := by
  -- We can not rewrite by `transpose`, because the default equation lemma has been replaced.
  fail_if_success rw [transpose]
  -- After using `funext`, rewriting by `transpose` uses `transpose_apply`.
  funext i j
  rw [transpose]
```
-/
syntax (name := eqns) "eqns" (ppSpace ident)* : attr

@[inherit_doc eqns]
initialize eqnsAttribute : NameMapExtension (Array Name) ←
  registerNameMapAttribute {
    name  := `eqns
    descr := "Overrides the equation lemmas for a declaration to the provided list"
    add   := fun
    | _, `(attr| eqns $[$names]*) =>
      names.mapM resolveGlobalConstNoOverloadWithInfo
    | _, _ => Lean.Elab.throwUnsupportedSyntax }

initialize Lean.Meta.registerGetEqnsFn (fun name => do
  pure (eqnsAttribute.find? (← getEnv) name))

end Std.Tactic
