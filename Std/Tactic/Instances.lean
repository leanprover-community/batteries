/-
Copyright (c) 2023 Kyle Miller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Miller
-/
import Lean

/-! # `#instances` command

The `#instances` command prints lists all instances that apply to the given type, if it is a class.
It is similar to `#synth` but it only does the very first step of the instance synthesis algorithm,
which is to enumerate potential instances.
-/

open Lean Elab Command Meta

namespace Std.Tactic.Instances

/-- `#instances term` prints all the instances for the given class.
For example, `#instances Add _` gives all `Add` instances, and `#instances Add Nat` gives the
`Nat` instance. The `term` can be any type that can appear in `[...]` binders.

Trailing underscores can be omitted, and `#instances Add` and `#instances Add _` are equivalent;
the command adds metavariables until the argument is no longer a function.

The `#instances` command is closely related to `#synth`, but `#synth` does the full
instance synthesis algorithm and `#instances` does the first step of finding potential instances. -/
elab "#instances " stx:term : command => runTermElabM fun _ => do
  let t ← Term.elabTerm stx none
  -- allow t to be universally quantified
  let t ← forallTelescope t fun xs t' => do
    -- Throw in missing arguments using metavariables. This only makes sense in the
    -- non-quantified case.
    let (_, _, t') ← lambdaMetaTelescope (← etaExpand t')
    mkForallFVars xs t'
  let insts ← Lean.Meta.SynthInstance.getInstances t
  if insts.isEmpty then
    logInfo m!"No instances"
  else
    let mut results := []
    for inst in insts do
      let e := inst.val
      -- Number the universe variables within each entry separately.
      let type ← withoutModifyingState do Term.levelMVarToParam (← inferType e)
      results := m!"{e} : {type}" :: results
    let instances := if insts.size == 1 then "instance" else "instances"
    logInfo m!"{insts.size} {instances}:\n\n{MessageData.joinSep results.reverse "\n"}"
