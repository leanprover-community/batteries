/-
Copyright (c) 2022 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Ebner, Moritz Roos
-/
module

public meta import Lean.Meta.Instances
public meta import Batteries.Tactic.Lint.Basic
public meta import Lean.Elab.Command
public meta import Lean.Linter.Basic
public meta import Lean.Server.InfoUtils
public meta import Batteries.Data.List.Basic

public meta section

section environmentLinters

namespace Batteries.Tactic.Lint
open Lean Meta

/--
Lints for instances with arguments that cannot be filled in, like
```
instance {α β : Type} [Group α] : Mul α where ...
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
end environmentLinters



section StandardLinters

/-- This function searches laterally to find the top level names of declarations (along with their
    syntax). Thanks Thomas Murrills!
    Note: This function picks up some internal names from e.g. `examples` (like `bla._example`)
    that it probably shouldn't. You should probably filter these using `(← getEnv).contains name`.
-/
partial def Lean.Elab.InfoTree.getTopLevelDeclsByBody : InfoTree → List (Name × Syntax) :=
  go none []
where
  go (ctx? : Option ContextInfo) (acc : List (Name × Syntax)) : InfoTree → List (Name × Syntax)
    | context ctx t => go (ctx.mergeIntoOuter? ctx?) acc t
    | node i ts => Id.run do
      if let .ofCustomInfo i := i then
        if i.value.typeName == ``Lean.Elab.Term.BodyInfo then
          if let some decl := ctx?.bind (·.parentDecl?) then
            return (decl, i.stx) :: acc -- don't descend into `ts`
      ts.foldl (init := acc) (go ctx?)
    | hole _ => acc



namespace Batteries.Linter
open Lean Elab Command Linter Std Meta

/-- Option for turning the `impossibleInstance'` linter on and off. -/
register_option linter.impossibleInstance' : Bool := {
  defValue := true
  descr := "Warn when an instance is found that can never be synthesized by typeclass synthesis."
}


/--
Lints for instances with arguments that cannot be filled in, like
```
instance {α β : Type} [Group α] : Mul α where ...
```
This is a syntax linter, i.e. it runs on your declarations as you write them.
-/
def impossibleInstance' : Linter where run cmdSyntax := do
  unless Linter.getLinterValue linter.impossibleInstance' (← Linter.getLinterOptions) do
    return
  /- todo use `withSetOptionIn` after `https://github.com/leanprover/lean4/pull/11313` has
     been resolved, to allow disabling this linter with
     `set_option linter.impossibleInstance false in`. -/
  let errorsFound1 := m!"This instance has at least one argument that is impossible \
    to infer for typeclass inference. Specifically\n"
  let errorsFound2 := m!"\nThese are arguments that are not instance-implicit and \
    appear neither in another instance-implicit argument nor the return type, so they can't \
    be filled in by typeclass inference."
  let test (declName : Name) : MetaM (Option MessageData) := do
    unless ← isInstance declName do return none
    forallTelescopeReducing (← inferType (← mkConstWithLevelParams declName)) fun args ty => do
    let argTys ← args.mapM inferType
    let impossibleArgs ← args.zipIdx.filterMapM fun (arg, i) => do
      let fv := arg.fvarId!
      if (← fv.getDecl).binderInfo.isInstImplicit then return none
      if ty.containsFVar fv then return none
      if argTys[i+1:].any (·.containsFVar fv) then return none
      let brackets : String × String := match (← fv.getDecl).binderInfo with
        | .implicit        => ("{", "}")
        | .strictImplicit  => ("⦃", "⦄")
        | .instImplicit    => ("[", "]")
        | .default         => ("(", ")")
      return some (m!"    argument {i+1}: "
        ++ s!"`{brackets.1}{←fv.getUserName} : {← inferType arg}{brackets.2}`")
    if impossibleArgs.isEmpty then return none
    return errorsFound1 ++ (Lean.MessageData.joinSep impossibleArgs.toList ", ") ++ errorsFound2
  /- We do the check for each (different) top level instance name we can get from the infotrees.
     Mostly this will only be one name, but for `mutual` blocks this will be more. -/
  let mut names : List (Name × Syntax) := []
  for t in ←getInfoTrees do
    names := t.getTopLevelDeclsByBody ++ names
  /- Each name shall only be checked once, so we remove duplicates. -/
  names := names.pwFilter (fun (a, _) (b, _) => a != b)
  /- the `getTopLevelDeclsByBody` function picks up some internal names from `examples` that it
     probably shouldn't. We filter these here. -/
  names := (← names.filterM (fun (name, _) => return (← getEnv).contains name))
  -- names := names.eraseDups -- todo only first elements duplicate remove
  for (name, stx) in names do
    /- check if the return type is class-valued,
       else the `nonClassInstance'` linter will lint against this. -/
    let constInfo ← (Lean.getConstInfo name)
    if not (← liftTermElabM (isClass? constInfo.type)).isSome then continue
    /- Now the actual linting check: -/
    let some lintmessage ← liftTermElabM (test name) | continue
    /- Use the range that actually corresponds to the `name` not to the whole mutual block: -/
    Linter.logLint linter.impossibleInstance' stx lintmessage
  return
initialize addLinter impossibleInstance'

/-- Option for turning the `nonClassInstance'` linter on and off. -/
register_option linter.nonClassInstance' : Bool := {
  defValue := true
  descr := "Warn when a declaration is found whose type is not a class but is marked as instance. "
}

/--
A linter for checking if any declaration whose type is not a class is marked as an instance.
-/
def nonClassInstance' : Linter where run cmdSyntax := do
  unless Linter.getLinterValue linter.nonClassInstance' (← Linter.getLinterOptions) do
    return
  /- todo use `withSetOptionIn` after `https://github.com/leanprover/lean4/pull/11313` has
     been resolved, to allow disabling this linter with
     `set_option linter.impossibleInstance false in`.
     Also add an `in` to the test in `BatteriesTest.lintTC.lean`. -/
  let test (declName : Name) : TermElabM (Option MessageData) := do
    if !(← isInstance declName) then return none
    let info ← getConstInfo declName
    if !(← isClass? info.type).isSome then
      return "This declaration should not be an instance as it is not class-valued. "
    return none
  /- We do the check for each (different) top level instance name we can get from the infotrees.
     Mostly this will only be one name, but for `mutual` blocks this will be more. -/
  let mut names : List (Name × Syntax) := []
  for t in ←getInfoTrees do
    names := t.getTopLevelDeclsByBody ++ names
  /- Each name shall only be checked once, so we remove duplicates. -/
  names := names.pwFilter (fun (a, _) (b, _) => a != b)
  /- the `getTopLevelDeclsByBody` function picks up some internal names from `examples` that it
     probably shouldn't. We filter these here. -/
  names := (← names.filterM (fun (name, _) => return (← getEnv).contains name))
  for (name, stx) in names do
    let some lintmessage ← liftTermElabM (test name) | continue
    Linter.logLint linter.nonClassInstance' stx lintmessage
  return

initialize addLinter nonClassInstance'

end Batteries.Linter
end StandardLinters
