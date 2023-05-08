/-
Copyright (c) 2023 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Lean.Server.CodeActions
import Std.Util.TermUnsafe

/-!
# Initial setup for hole commands

This declares an attribute `@[hole_command]` which collects code actions which will be called
on each occurrence of a hole (`_`, `?_` or `sorry`).
-/
namespace Std.Tactic

open Lean Elab Server Lsp RequestM Snapshots

/-- A hole command extension. -/
abbrev HoleCommand :=
  CodeActionParams → Snapshot →
  (ctx : ContextInfo) → (hole : TermInfo) → RequestM (Array LazyCodeAction)

namespace HoleCommand

/-- Read a `positivity` extension from a declaration of the right type. -/
def mkHoleCommand (n : Name) : ImportM HoleCommand := do
  let { env, opts, .. } ← read
  IO.ofExcept <| unsafe env.evalConstCheck HoleCommand opts ``HoleCommand n

/-- An extension which collects all the hole commands. -/
initialize holeCommandExt :
    PersistentEnvExtension Name (Name × HoleCommand) (Array Name × Array HoleCommand) ←
  registerPersistentEnvExtension {
    mkInitial := pure (#[], #[])
    addImportedFn := fun as => return (#[], ← as.foldlM (init := #[]) fun m as =>
      as.foldlM (init := m) fun m a => return m.push (← mkHoleCommand a))
    addEntryFn := fun (s₁, s₂) (n₁, n₂) => (s₁.push n₁, s₂.push n₂)
    exportEntriesFn := (·.1)
  }

initialize
  registerBuiltinAttribute {
    name := `hole_command
    descr := "Declare a new hole command, to appear in the code actions on ?_ and _"
    applicationTime := .afterCompilation
    add := fun decl stx kind => do
      Attribute.Builtin.ensureNoArgs stx
      unless kind == AttributeKind.global do
        throwError "invalid attribute 'hole_command', must be global"
      if (IR.getSorryDep (← getEnv) decl).isSome then return -- ignore in progress definitions
      modifyEnv (holeCommandExt.addEntry · (decl, ← mkHoleCommand decl))
  }
