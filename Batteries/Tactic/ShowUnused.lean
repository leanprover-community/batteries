/-
Copyright (c) 2024 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Lean.Util.FoldConsts
import Lean.Linter.UnusedVariables

/-!
# The `#show_unused` command

`#show_unused decl1 decl2 ..` will highlight every theorem or definition in the current file
not involved in the definition of declarations `decl1`, `decl2`, etc. The result is shown
both in the message on `#show_unused`, as well as on the declarations themselves.
-/

namespace Batteries.Tactic.ShowUnused
open Lean Elab Command

variable (env : Environment) in
private partial def visit (n : Name) : StateM NameSet Unit := do
  if (← get).contains n then
    modify (·.erase n)
    let rec visitExpr (e : Expr) : StateM NameSet Unit := e.getUsedConstants.forM visit
    match env.find? n with
    | some (ConstantInfo.axiomInfo v)  => visitExpr v.type
    | some (ConstantInfo.defnInfo v)   => visitExpr v.type *> visitExpr v.value
    | some (ConstantInfo.thmInfo v)    => visitExpr v.type *> visitExpr v.value
    | some (ConstantInfo.opaqueInfo v) => visitExpr v.type *> visitExpr v.value
    | some (ConstantInfo.quotInfo _)   => pure ()
    | some (ConstantInfo.ctorInfo v)   => visitExpr v.type
    | some (ConstantInfo.recInfo v)    => visitExpr v.type
    | some (ConstantInfo.inductInfo v) => visitExpr v.type *> v.ctors.forM visit
    | none                             => pure ()

/--
`#show_unused decl1 decl2 ..` will highlight every theorem or definition in the current file
not involved in the definition of declarations `decl1`, `decl2`, etc. The result is shown
both in the message on `#show_unused`, as well as on the declarations themselves.
```
def foo := 1
def baz := 2
def bar := foo
#show_unused bar -- highlights `baz`
```
-/
elab tk:"#show_unused" ids:(ppSpace colGt ident)* : command => do
  let ns ← ids.mapM fun s => liftCoreM <| realizeGlobalConstNoOverloadWithInfo s
  let env ← getEnv
  let decls := env.constants.map₂.foldl (fun m n _ => m.insert n) {}
  let mut unused := #[]
  let fileMap ← getFileMap
  for c in ((ns.forM (visit env)).run decls).2 do
    if let some { selectionRange := range, .. } := declRangeExt.find? env c then
      unused := unused.push (c, {
        start := fileMap.ofPosition range.pos
        stop := fileMap.ofPosition range.endPos
      })
  unused := unused.qsort (·.2.start < ·.2.start)
  let pos := fileMap.toPosition <| (tk.getPos? <|> (← getRef).getPos?).getD 0
  let pfx := m!"#show_unused (line {pos.line}) says:\n"
  let post := m!" is not used transitively by \
    {← ns.mapM (MessageData.ofConst <$> mkConstWithLevelParams ·)}"
  for (c, range) in unused do
    logWarningAt (Syntax.ofRange range) <|
      .tagged Linter.linter.unusedVariables.name <|
        m!"{pfx}{MessageData.ofConst (← mkConstWithLevelParams c)}{post}"
  if unused.isEmpty then
    logInfoAt tk "No unused definitions"
  else
    logWarningAt tk <| m!"unused definitions in this file:\n" ++
      m!"\n".joinSep (← unused.toList.mapM (toMessageData <$> mkConstWithLevelParams ·.1))
