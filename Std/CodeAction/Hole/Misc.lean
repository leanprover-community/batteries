/-
Copyright (c) 2023 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Std.Lean.Position
import Std.CodeAction.Hole.Basic

/-!
# Miscellaneous hole code actions

This declares some basic hole code actions, using the `@[hole_code_action]` API.
-/
namespace Std.CodeAction

open Lean Server RequestM Meta

/-- Return the syntax stack leading to `target` from `root`, if one exists. -/
def findStack? (root target : Syntax) : Option Syntax.Stack := do
  let range ← target.getRange?
  root.findStack? (·.getRange?.any (·.includes range))
    (fun s => s.getKind == target.getKind && s.getRange? == range)

/-- Constructs a hole with a kind matching the provided hole elaborator.  -/
def holeKindToHoleString : (elaborator : Name) → (synthName : String) → String
  | ``Elab.Term.elabSyntheticHole, name => "?" ++ name
  | ``Elab.Term.elabSorry, _ => "sorry"
  | _, _ => "_"

/--
Hole code action used to fill in a structure's field when specifying an instance.

In the following:
```lean
instance : Monad Id := _
```

invoking the hole code action "Generate a skeleton for the structure under construction." produces:
```lean
instance : Monad Id := {
  map := _
  mapConst := _
  pure := _
  seq := _
  seqLeft := _
  seqRight := _
  bind := _
}
```
-/
@[hole_code_action] partial def instanceStub : HoleCodeAction := fun params snap ctx info => do
  let some ty := info.expectedType? | return #[]
  let .const name _ := (← info.runMetaM ctx (whnf ty)).getAppFn | return #[]
  unless isStructure snap.env name do return #[]
  let eager := {
    title := "Generate a skeleton for the structure under construction."
    kind? := "quickfix"
    isPreferred? := true
  }
  let doc ← readDoc
  pure #[{
    eager
    lazy? := some do
      let useWhere := do
        let _ :: (stx, _) :: _ ← findStack? snap.stx info.stx | none
        guard (stx.getKind == ``Parser.Command.declValSimple)
        stx[0].getPos?
      let holePos := useWhere.getD info.stx.getPos?.get!
      let (indent, isStart) := findIndentAndIsStart doc.meta.text.source holePos
      let indent := "\n".pushn ' ' indent
      let mut str := if useWhere.isSome then "where" else "{"
      let mut first := useWhere.isNone && isStart
      for field in collectFields snap.env name #[] do
        if first then
          str := str ++ " "
          first := false
        else
          str := str ++ indent ++ "  "
        let field := toString field
        str := str ++ s!"{field} := {holeKindToHoleString info.elaborator field}"
      if useWhere.isNone then
        if isStart then
          str := str ++ " }"
        else
          str := str ++ indent ++ "}"
      pure { eager with
        edit? := some <| .ofTextEdit params.textDocument.uri {
          range := doc.meta.text.utf8RangeToLspRange ⟨holePos, info.stx.getTailPos?.get!⟩
          newText := str
        }
      }
  }]
where
  /-- Returns the fields of a structure, unfolding parent structures. -/
  collectFields (env : Environment) (structName : Name) (fields : Array Name) : Array Name :=
    (getStructureFields env structName).foldl (init := fields) fun fields field =>
      match isSubobjectField? env structName field with
      | some substructName => collectFields env substructName fields
      | none => fields.push field

/-- Returns the explicit arguments given a type. -/
def getExplicitArgs : Expr → Array Name → Array Name
  | .forallE n _ body bi, args =>
    getExplicitArgs body <| if bi.isExplicit then args.push n else args
  | _, args => args

/--
Invoking hole code action "Generate a list of equations for a recursive definition" in the
following:
```lean
def foo : Expr → Unit := _
```

produces:

```lean
def foo : Expr → Unit := fun
  | .bvar deBruijnIndex => _
  | .fvar fvarId => _
  | .mvar mvarId => _
  | .sort u => _
  | .const declName us => _
  | .app fn arg => _
  | .lam binderName binderType body binderInfo => _
  | .forallE binderName binderType body binderInfo => _
  | .letE declName type value body nonDep => _
  | .lit _ => _
  | .mdata data expr => _
  | .proj typeName idx struct => _
```

-/
@[hole_code_action] def eqnStub : HoleCodeAction := fun params snap ctx info => do
  let some ty := info.expectedType? | return #[]
  let .forallE _ dom .. ← info.runMetaM ctx (whnf ty) | return #[]
  let .const name _ := (← info.runMetaM ctx (whnf dom)).getAppFn | return #[]
  let some (.inductInfo val) := snap.env.find? name | return #[]
  let eager := {
    title := "Generate a list of equations for a recursive definition."
    kind? := "quickfix"
  }
  let doc ← readDoc
  pure #[{
    eager
    lazy? := some do
      let holePos := info.stx.getPos?.get!
      let (indent, isStart) := findIndentAndIsStart doc.meta.text.source holePos
      let mut str := "fun"
      let indent := "\n".pushn ' ' (if isStart then indent else indent + 2)
      for ctor in val.ctors do
        let some (.ctorInfo ci) := snap.env.find? ctor | panic! "bad inductive"
        let ctor := toString (ctor.updatePrefix .anonymous)
        str := str ++ indent ++ s!"| .{ctor}"
        for arg in getExplicitArgs ci.type #[] do
          str := str ++ if arg.hasNum || arg.isInternal then " _" else s!" {arg}"
        str := str ++ s!" => {holeKindToHoleString info.elaborator ctor}"
      pure { eager with
        edit? := some <|.ofTextEdit params.textDocument.uri {
          range := doc.meta.text.utf8RangeToLspRange ⟨holePos, info.stx.getTailPos?.get!⟩
          newText := str
        }
      }
  }]
