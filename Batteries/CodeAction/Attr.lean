/-
Copyright (c) 2023 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Lean.Server.CodeActions.Basic

/-!
# Initial setup for code action attributes

* `@[hole_code_action]` and `@[command_code_action]` now live in the Lean repository,
  and are builtin.

* Attribute `@[tactic_code_action]` collects code actions which will be called
  on each occurrence of a tactic.
-/
namespace Std.CodeAction

open Lean Elab Server Lsp RequestM Snapshots

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
          let args ← args.mapM realizeGlobalConstNoOverloadWithInfo
          if (IR.getSorryDep (← getEnv) decl).isSome then return -- ignore in progress definitions
          modifyEnv (tacticCodeActionExt.addEntry · (⟨decl, args⟩, ← mkTacticCodeAction decl))
      | _ => pure ()
  }
