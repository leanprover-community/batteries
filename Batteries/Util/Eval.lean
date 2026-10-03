/-
Copyright (c) 2026 Robin Arnez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robin Arnez
-/
module

public meta import Lean.Util.CollectLevelParams
public meta import Lean.Compiler.Options
public meta import Lean.AddDecl
public meta import Lean.Meta.Check

public meta section

/--
An alternative of `evalExpr` that also errors in the presence of `sorry` unless `allowSorry` is
true. If there is an alternative command that does allow `sorry`s, you can specify it in
`alternative?`.
-/
unsafe def Lean.Meta.evalExprWithSorryCheck (α) (type value : Expr)
    (safety := DefinitionSafety.safe) (checkMeta : Bool := true)
    (allowSorry : Bool := false) (alternative? : Option String := none) : MetaM α :=
  withoutModifyingEnv do
    -- Avoid waiting for all prior compilation if only imported constants are referenced. This is a
    -- very common case for tactic configurations (`Lean.Elab.Tactic.Config`).
    if value.getUsedConstants.all (← getEnv).isImportedConst then
      modifyEnv fun env => env.importEnv?.getD env

    -- Private name to ensure we do not check for deps being imported publicly
    let name := mkPrivateName (← getEnv) (← mkFreshUserName `_tmp)
    let value ← instantiateMVars value
    let us := collectLevelParams {} value |>.params
    if value.hasMVar then
      throwError "failed to evaluate expression, it contains metavariables{indentExpr value}"
    -- We assume that the type is correct here; otherwise we'll get a kernel error
    let decl := Declaration.defnDecl {
      name, levelParams := us.toList, type
      value, hints := ReducibilityHints.opaque,
      safety
    }
    modifyEnv (markMeta · name)
    -- compilation will invariably wait on `checked`
    let _ ← traceBlock "compiler env" (← getEnv).checked
    -- now that we've already waited, async would just introduce (minor) overhead and trigger
    -- `Task.get` blocking debug code
    withOptions (Elab.async.set · false) do
    withOptions (Compiler.compiler.postponeCompile.set · false) do
    withOptions (Compiler.compiler.relaxedMetaCheck.set · true) do
      addDecl decl
      unless allowSorry do
        let axioms ← collectAxioms name
        if axioms.contains ``sorryAx then
          let mut msg : MessageData := "\
            Aborting evaluation since the expression depends on the `sorry` axiom, \
            which can lead to runtime instability and crashes."
          if let some alternative := alternative? then
            msg := m!"{msg}\n\n\
              To attempt to evaluate anyway despite the risks, use the `{alternative}` command."
          throwError msg
      compileDecl decl
      evalConst (checkMeta := checkMeta) α name
