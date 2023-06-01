/-
Copyright (c) 2023 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Lean.Server.CodeActions
import Std.Util.TermUnsafe

/-!
# Initial setup for code action attributes

* Attribute `@[hole_code_action]` collects code actions which will be called
  on each occurrence of a hole (`_`, `?_` or `sorry`).

* Attribute `@[tactic_code_action]` collects code actions which will be called
  on each occurrence of a tactic.

* Attribute `@[command_code_action]` collects code actions which will be called
  on each occurrence of a command.
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

/-- A tactic code action extension. -/
abbrev TacticCodeAction :=
  CodeActionParams → Snapshot →
  (ctx : ContextInfo) → (stack : Syntax.Stack) → (node : InfoTree) →
  RequestM (Array LazyCodeAction)

/-- A tactic code action extension. -/
abbrev TacticSeqCodeAction :=
  CodeActionParams → Snapshot →
  (ctx : ContextInfo) → (i : Nat) → (stack : Syntax.Stack) → (goals : List MVarId) →
  RequestM (Array LazyCodeAction)

/-- Read a tactic code action from a declaration of the right type. -/
def mkTacticCodeAction (n : Name) : ImportM TacticCodeAction := do
  let { env, opts, .. } ← read
  IO.ofExcept <| unsafe env.evalConstCheck TacticCodeAction opts ``TacticCodeAction n

/-- Read a tacticSeq code action from a declaration of the right type. -/
def mkTacticSeqCodeAction (n : Name) : ImportM TacticSeqCodeAction := do
  let { env, opts, .. } ← read
  IO.ofExcept <| unsafe env.evalConstCheck TacticSeqCodeAction opts ``TacticSeqCodeAction n

/-- An entry in the tactic code actions extension, containing the attribute arguments. -/
structure TacticCodeActionEntry where
  /-- The declaration to tag -/
  declName : Name
  /-- The tactic kinds that this extension supports. If empty it is called on all tactic kinds. -/
  tacticKinds : Array Name
  deriving Inhabited

/-- The state of the tactic code actions extension. -/
structure TacticCodeActions where
  /-- The list of tactic code actions to apply on any tactic. -/
  onAnyTactic : Array TacticCodeAction := {}
  /-- The list of tactic code actions to apply when a particular tactic kind is highlighted. -/
  onTactic : NameMap (Array TacticCodeAction) := {}
  deriving Inhabited

/-- Insert a tactic code action entry into the `TacticCodeActions` structure. -/
def TacticCodeActions.insert (self : TacticCodeActions)
    (tacticKinds : Array Name) (action : TacticCodeAction) : TacticCodeActions :=
  if tacticKinds.isEmpty then
    { self with onAnyTactic := self.onAnyTactic.push action }
  else
    { self with onTactic := tacticKinds.foldl (init := self.onTactic) fun m a =>
        m.insert a ((m.findD a #[]).push action) }

/-- An extension which collects all the tactic code actions. -/
initialize tacticSeqCodeActionExt :
    PersistentEnvExtension Name (Name × TacticSeqCodeAction)
      (Array Name × Array TacticSeqCodeAction) ←
  registerPersistentEnvExtension {
    mkInitial := pure (#[], #[])
    addImportedFn := fun as => return (#[], ← as.foldlM (init := #[]) fun m as =>
      as.foldlM (init := m) fun m a => return m.push (← mkTacticSeqCodeAction a))
    addEntryFn := fun (s₁, s₂) (n₁, n₂) => (s₁.push n₁, s₂.push n₂)
    exportEntriesFn := (·.1)
  }

/-- An extension which collects all the tactic code actions. -/
initialize tacticCodeActionExt :
    PersistentEnvExtension TacticCodeActionEntry (TacticCodeActionEntry × TacticCodeAction)
      (Array TacticCodeActionEntry × TacticCodeActions) ←
  registerPersistentEnvExtension {
    mkInitial := pure (#[], {})
    addImportedFn := fun as => return (#[], ← as.foldlM (init := {}) fun m as =>
      as.foldlM (init := m) fun m ⟨name, kinds⟩ =>
        return m.insert kinds (← mkTacticCodeAction name))
    addEntryFn := fun (s₁, s₂) (e, n₂) => (s₁.push e, s₂.insert e.tacticKinds n₂)
    exportEntriesFn := (·.1)
  }

/--
This attribute marks a code action, which is used to suggest new tactics or replace existing ones.

* `@[tactic_code_action]`: This is a code action which applies to the spaces between tactics,
  to suggest a new tactic to change the goal state.

* `@[tactic_code_action kind]`: This is a code action which applies to applications of the tactic
  `kind` (a tactic syntax kind), which can replace the tactic or insert things before or after it.

* `@[tactic_code_action kind₁ kind₂]`: shorthand for
  `@[tactic_code_action kind₁, tactic_code_action kind₂]`.

* `@[tactic_code_action *]`: This is a tactic code action that applies to all tactics.
  Use sparingly.
-/
syntax (name := tactic_code_action) "tactic_code_action" ("*" <|> (ppSpace ident)*) : attr

initialize
  registerBuiltinAttribute {
    name := `tactic_code_action
    descr := "Declare a new tactic code action, to appear in the code actions on tactics"
    applicationTime := .afterCompilation
    add := fun decl stx kind => do
      unless kind == AttributeKind.global do
        throwError "invalid attribute 'tactic_code_action', must be global"
      match stx with
      | `(attr| tactic_code_action *) =>
        if (IR.getSorryDep (← getEnv) decl).isSome then return -- ignore in progress definitions
        modifyEnv (tacticCodeActionExt.addEntry · (⟨decl, #[]⟩, ← mkTacticCodeAction decl))
      | `(attr| tactic_code_action $[$args]*) =>
        if args.isEmpty then
          if (IR.getSorryDep (← getEnv) decl).isSome then return -- ignore in progress definitions
          modifyEnv (tacticSeqCodeActionExt.addEntry · (decl, ← mkTacticSeqCodeAction decl))
        else
          let args ← args.mapM resolveGlobalConstNoOverloadWithInfo
          if (IR.getSorryDep (← getEnv) decl).isSome then return -- ignore in progress definitions
          modifyEnv (tacticCodeActionExt.addEntry · (⟨decl, args⟩, ← mkTacticCodeAction decl))
      | _ => pure ()
  }

/-- A command code action extension. -/
abbrev CommandCodeAction :=
  CodeActionParams → Snapshot → (ctx : ContextInfo) → (node : InfoTree) →
  RequestM (Array LazyCodeAction)

/-- Read a command code action from a declaration of the right type. -/
def mkCommandCodeAction (n : Name) : ImportM CommandCodeAction := do
  let { env, opts, .. } ← read
  IO.ofExcept <| unsafe env.evalConstCheck CommandCodeAction opts ``CommandCodeAction n

/-- An entry in the command code actions extension, containing the attribute arguments. -/
structure CommandCodeActionEntry where
  /-- The declaration to tag -/
  declName : Name
  /-- The command kinds that this extension supports.
  If empty it is called on all command kinds. -/
  cmdKinds : Array Name
  deriving Inhabited

/-- The state of the command code actions extension. -/
structure CommandCodeActions where
  /-- The list of command code actions to apply on any command. -/
  onAnyCmd : Array CommandCodeAction := {}
  /-- The list of command code actions to apply when a particular command kind is highlighted. -/
  onCmd : NameMap (Array CommandCodeAction) := {}
  deriving Inhabited

/-- Insert a command code action entry into the `CommandCodeActions` structure. -/
def CommandCodeActions.insert (self : CommandCodeActions)
    (tacticKinds : Array Name) (action : CommandCodeAction) : CommandCodeActions :=
  if tacticKinds.isEmpty then
    { self with onAnyCmd := self.onAnyCmd.push action }
  else
    { self with onCmd := tacticKinds.foldl (init := self.onCmd) fun m a =>
        m.insert a ((m.findD a #[]).push action) }

/-- An extension which collects all the command code actions. -/
initialize cmdCodeActionExt :
    PersistentEnvExtension CommandCodeActionEntry (CommandCodeActionEntry × CommandCodeAction)
      (Array CommandCodeActionEntry × CommandCodeActions) ←
  registerPersistentEnvExtension {
    mkInitial := pure (#[], {})
    addImportedFn := fun as => return (#[], ← as.foldlM (init := {}) fun m as =>
      as.foldlM (init := m) fun m ⟨name, kinds⟩ =>
        return m.insert kinds (← mkCommandCodeAction name))
    addEntryFn := fun (s₁, s₂) (e, n₂) => (s₁.push e, s₂.insert e.cmdKinds n₂)
    exportEntriesFn := (·.1)
  }

/--
This attribute marks a code action, which is used to suggest new tactics or replace existing ones.

* `@[command_code_action kind]`: This is a code action which applies to applications of the command
  `kind` (a command syntax kind), which can replace the command or insert things before or after it.

* `@[command_code_action kind₁ kind₂]`: shorthand for
  `@[command_code_action kind₁, command_code_action kind₂]`.

* `@[command_code_action]`: This is a command code action that applies to all commands.
  Use sparingly.
-/
syntax (name := command_code_action) "command_code_action" (ppSpace ident)* : attr

initialize
  registerBuiltinAttribute {
    name := `command_code_action
    descr := "Declare a new command code action, to appear in the code actions on commands"
    applicationTime := .afterCompilation
    add := fun decl stx kind => do
      unless kind == AttributeKind.global do
        throwError "invalid attribute 'command_code_action', must be global"
      let `(attr| command_code_action $args*) := stx | return
      let args ← args.mapM resolveGlobalConstNoOverloadWithInfo
      if (IR.getSorryDep (← getEnv) decl).isSome then return -- ignore in progress definitions
      modifyEnv (cmdCodeActionExt.addEntry · (⟨decl, args⟩, ← mkCommandCodeAction decl))
  }
