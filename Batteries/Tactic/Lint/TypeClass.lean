/-
Copyright (c) 2022 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Ebner, Thomas Murrills, Moritz Roos
-/
module

public import Batteries.Tactic.Lint.Basic
public import Lean.Linter.Basic
public meta import Lean.Elab.Command
public meta import Batteries.Lean.Position
public meta import Batteries.Lean.Meta.Expr

public meta section

open Lean Meta Elab Command

/-! ### Environment Linters -/

namespace Batteries.Tactic.Lint

/--
Lints for instances with arguments that cannot be filled in, like
```
instance impossible {α β : Type} [Inhabited α] : Nonempty α := ⟨default⟩
```
-/
@[env_linter] def impossibleInstance : Linter where
  noErrorsFound := "No instance has arguments that are impossible to infer"
  errorsFound := "SOME INSTANCES HAVE ARGUMENTS THAT ARE IMPOSSIBLE TO INFER
These are arguments that are not instance-implicit and do not appear in
another instance-implicit argument or the return type."
  test declName := do
    unless ← isInstance declName do return none
    forallTelescopeReducing (← inferType (← mkConstWithLevelParams declName)) fun args ty => do
    let argTys ← args.mapM inferType
    let impossibleArgs ← args.zipIdx.filterMapM fun (arg, i) => do
      let fv := arg.fvarId!
      if (← fv.getDecl).binderInfo.isInstImplicit then return none
      if ty.containsFVar fv then return none
      if argTys[i+1:].any (·.containsFVar fv) then return none
      return some m!"argument {i+1} {arg} : {← inferType arg}"
    if impossibleArgs.isEmpty then return none
    addMessageContextFull <| .joinSep impossibleArgs.toList ", "

/--
A linter for checking if any declaration whose type is not a class is marked as an instance.
-/
@[env_linter] def nonClassInstance : Linter where
  noErrorsFound := "No instances of non-classes"
  errorsFound := "INSTANCES OF NON-CLASSES"
  test declName := do
    if !(← isInstance declName) then return none
    let info ← getConstInfo declName
    if !(← isClass? info.type).isSome then return "should not be an instance"
    return none

end Batteries.Tactic.Lint

/-! ### Syntax Linters -/

/-- Pretty-prints a local declaration and its type as a binder,
using the appropriate brackets given its `BinderInfo`. Example output: `{α : Type}`.

Returns `none` for let decls. -/
protected def Lean.LocalDecl.ppAsBinder : LocalDecl → Option MessageData
  | .ldecl .. => none
  | .cdecl _ fvarId _ type binderInfo _ =>
    let (lBracket, rBracket) : String × String := match binderInfo with
      | .implicit       => ("{", "}")
      | .strictImplicit => ("⦃", "⦄")
      | .instImplicit   => ("[", "]")
      | .default        => ("(", ")")
    some <| .bracket lBracket m!"{mkFVar fvarId} : {type}" rBracket

/-- Pretty-prints a free variable and its type as a binder,
using the appropriate brackets given its `BinderInfo`. Example output: `{α : Type}`.

Returns `none` for let decls. -/
@[inline]
protected def Lean.FVarId.ppAsBinder (fvarId : FVarId) : MetaM (Option MessageData) :=
  return (← fvarId.getDecl).ppAsBinder

namespace Batteries.Linter

open Linter Std

/-- The `impossibleInstance` linter flags instances that can never be synthesized by typeclass
synthesis. Setting this option to `false` will disable this linter. -/
register_option linter.impossibleInstance : Bool := {
  defValue := true
  descr := "Warn when an instance is found that can never be synthesized by typeclass synthesis."
}

/--
Lints for instances with arguments that cannot be filled in, like
```
instance impossible {α β : Type} [Inhabited α] : Nonempty α := ⟨default⟩
```
-/
def impossibleInstance : Linter where run := withSetOptionIn fun cmd => do
  unless getLinterValue linter.impossibleInstance (← getLinterOptions) do
    return
  if ← MonadLog.hasErrors then
    return
  let some pos := cmd.getPos? | return
  let env ← getEnv
  /- We only consider instances created within the current command, and rely on `isInstanceCore` to
  avoid `liftCoreM`. -/
  let decls := pos.getDeclsAfter env (← getFileMap) |>.filter (isInstanceCore env)
  unless decls.isEmpty do
    /- We do the check for each instance we can find from the current command. Mostly this will
    only be one name, but for `mutual` blocks this will be more. -/
    for declName in decls do
      let cinfo ← getConstInfo declName
      -- Performantly check if any non-instance binder is unused.
      if cinfo.type.hasUnusedForallBindersWhere fun bi _ => !bi.isInstImplicit then liftTermElabM do
        /- If the return type is not class valued (but an instance), the `nonClassInstance`
        linter will already put a message on this declaration, so we skip it here in that case. -/
        if (← isClass? cinfo.type).isSome then
        forallTelescope cinfo.type fun args ty => do
          -- Find the fvars used in the type and any instance implicit argument, transitively.
          let getInitialPossibleFVars := do
            ty.collectFVars
            for arg in args do
              if (← arg.fvarId!.getBinderInfo).isInstImplicit then
                /- The fvarIds in the `CollectFVars.State` should be our possible args. As such, we
                start by adding the instance arguments to the state, rather than computing the
                dependencies of their types. -/
                modifyThe CollectFVars.State (·.add arg.fvarId!)
          let possibleFVars ← (·.2) <$> getInitialPossibleFVars.run {}
          -- Transitively include dependencies.
          let possibleFVars ← possibleFVars.addDependencies
          let mut impossibleArgMsgs := #[]
          for arg in args, i in 1...* do
            unless possibleFVars.fvarSet.contains arg.fvarId! do
              let some binder ← arg.fvarId!.ppAsBinder | continue
              impossibleArgMsgs := impossibleArgMsgs.push <|
                indentD m!"argument {i}: `{binder}`"
          if impossibleArgMsgs.isEmpty then return -- Should not be reachable.
          withDeclRef? declName do
            Linter.logLint linter.impossibleInstance (← getRef) m!"\
              This instance has {impossibleArgMsgs.size} \
              argument{if impossibleArgMsgs.size = 1 then "" else "s"} that cannot be \
              inferred using typeclass synthesis. Specifically\n\
              {.joinSep impossibleArgMsgs.toList .nil}\n\n\
              These arguments are not instance-implicit and appear neither in another \
              instance-implicit argument nor the return type, so they cannot be inferred using \
              typeclass synthesis."

initialize addLinter impossibleInstance

/-- The `nonClassInstance` linter flags declarations marked as `instance` but whose type
is not a class. Setting this option to `false` will disable this linter. -/
register_option linter.nonClassInstance : Bool := {
  defValue := true
  descr := "Warn when a declaration is found whose type is not a class but is marked as instance. "
}

/--
A linter for checking if any declaration whose type is not a class is marked as an instance.
-/
def nonClassInstance : Linter where run := withSetOptionIn fun cmd => do
  unless getLinterValue linter.nonClassInstance (← getLinterOptions) do
    return
  if ← MonadLog.hasErrors then
    return
  let some pos := cmd.getPos? | return
  let env ← getEnv
  /- We do the check for each instance that is associated with the current command.
  Mostly this will only be one name, but for `mutual` blocks this will be more. We use
  `isInstanceCore` to avoid a `liftCoreM`. -/
  let decls := pos.getDeclsAfter env (← getFileMap) |>.filter (isInstanceCore env)
  unless decls.isEmpty do liftTermElabM do
    for decl in decls do
      unless (← isClass? (← getConstInfo decl).type).isSome do
        withDeclRef? decl do
          Linter.logLint linter.nonClassInstance (← getRef)
            m!"The declaration `{.ofConstName decl}` should not be an instance \
            as it is not class-valued."

initialize addLinter nonClassInstance

end Batteries.Linter
