/-
Copyright (c) 2023 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Lean.Server.CodeActions
import Std.Util.TermUnsafe

/-!
# Initial setup for hole commands

This declares an attribute `@[hole_code_action]` which collects code actions which will be called
on each occurrence of a hole (`_`, `?_` or `sorry`).
-/
namespace Std.CodeAction

open Lean Elab Server Lsp RequestM Snapshots

/-- A hole code action extension. -/
abbrev HoleCodeAction :=
  CodeActionParams → Snapshot →
  (ctx : ContextInfo) → (hole : TermInfo) → RequestM (Array LazyCodeAction)

/-- Read a hole code action from a declaration of the right type. -/
def mkHoleCodeAction (n : Name) : ImportM HoleCodeAction := do
  let { env, opts, .. } ← read
  IO.ofExcept <| unsafe env.evalConstCheck HoleCodeAction opts ``HoleCodeAction n

/-- An extension which collects all the hole code actions. -/
initialize holeCodeActionExt :
    PersistentEnvExtension Name (Name × HoleCodeAction) (Array Name × Array HoleCodeAction) ←
  registerPersistentEnvExtension {
    mkInitial := pure (#[], #[])
    addImportedFn := fun as => return (#[], ← as.foldlM (init := #[]) fun m as =>
      as.foldlM (init := m) fun m a => return m.push (← mkHoleCodeAction a))
    addEntryFn := fun (s₁, s₂) (n₁, n₂) => (s₁.push n₁, s₂.push n₂)
    exportEntriesFn := (·.1)
  }

initialize
  registerBuiltinAttribute {
    name := `hole_code_action
    descr := "Declare a new hole code action, to appear in the code actions on ?_ and _"
    applicationTime := .afterCompilation
    add := fun decl stx kind => do
      Attribute.Builtin.ensureNoArgs stx
      unless kind == AttributeKind.global do
        throwError "invalid attribute 'hole_code_action', must be global"
      if (IR.getSorryDep (← getEnv) decl).isSome then return -- ignore in progress definitions
      modifyEnv (holeCodeActionExt.addEntry · (decl, ← mkHoleCodeAction decl))
  }
