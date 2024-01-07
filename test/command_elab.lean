import Std.Tactic.RunCmd
import Std.Tactic.GuardMsgs
import Std.Lean.Elab.Command
import Lean.Meta.Tactic.Simp
import Std.Tactic.Ext

open Lean Elab Command

/-- error: type mismatch for 'maxHeartbeats' -/
#guard_msgs in run_cmd trySetOptions #[⟨`maxHeartbeats, true⟩]

/-
Verify that `trySetOptions` and `tryEraseAttrs` properly
set options, erase attributes, and skip nonexistent ones
-/

run_cmd do
  trySetOptions #[
    ⟨`push_neg.use_distrib, true⟩,
    ⟨`warningAsError, true⟩
  ]
  tryEraseAttrs #[
    ⟨`simp, #[`ne_eq, `foo]⟩,
    ⟨`ext, #[`Prod.ext, `foo]⟩,
    ⟨`instance, #[
      `Int.instDivInt_1,`Int.instDivInt,
      `EuclideanDomain.instDiv, `Nat.instDivNat
    ]⟩,
    ⟨`norm_num, #[`Mathlib.Meta.NormNum.evalNatDvd]⟩
  ]

/-- info: true -/
#guard_msgs(info) in run_cmd
  logInfo <| repr <| (← getOptions).get `warningAsError false

/-- info: false -/
#guard_msgs(info) in run_cmd-- true
  logInfo <| repr <| (← getOptions).get `push_neg.use_distrib false

/-- info: #[Lean.Meta.Origin.decl `ne_eq false] -/
#guard_msgs(info) in run_cmd
  let thms := Lean.Meta.simpExtension.getState (← getEnv)
  logInfo <| repr <| thms.erased.fold Array.push Array.empty

/-- info: #[`Prod.ext] -/
#guard_msgs(info) in run_cmd-- #[`Prod.ext]
  let thms := Std.Tactic.Ext.extExtension.getState (← getEnv)
  logInfo <| repr <| thms.erased.fold Array.push Array.empty

/-- info: #[`Int.instDivInt, `Nat.instDivNat] -/
#guard_msgs(info) in run_cmd
  let insts ← liftCoreM Lean.Meta.getErasedInstances
  logInfo <| repr <| insts.fold Array.push Array.empty
