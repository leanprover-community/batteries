/-
Copyright (c) 2023 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Lean.Elab.BuiltinTerm
import Lean.Elab.BuiltinNotation
import Lean.Server.InfoUtils
import Batteries.CodeAction.Attr

/-!
# Initial setup for code actions

This declares a code action provider that calls all `@[hole_code_action]` definitions
on each occurrence of a hole (`_`, `?_` or `sorry`).

(This is in a separate file from `Batteries.CodeAction.Hole.Attr` so that the server does not
attempt to use this code action provider when browsing the `Batteries.CodeAction.Hole.Attr` file
itself.)
-/
namespace Std.CodeAction

open Lean Elab Term Server RequestM

/--
The return value of `findTactic?`.
This is the syntax for which code actions will be triggered.
-/
inductive FindTacticResult
  /-- The nearest enclosing tactic is a tactic, with the given syntax stack. -/
  | tactic : Syntax.Stack → FindTacticResult
  /-- The cursor is between tactics, and the nearest enclosing range is a tactic sequence.
  Code actions will insert tactics at index `insertIdx` into the syntax
  (which is a nullNode of `tactic;*` inside a `tacticSeqBracketed` or `tacticSeq1Indented`). -/
  | tacticSeq : (preferred : Bool) → (insertIdx : Nat) → Syntax.Stack → FindTacticResult

/--
Find the syntax on which to trigger tactic code actions.
This is a pure syntax pass, without regard to elaboration information.

* `preferred : String.Pos → Bool`: used to select "preferred `tacticSeq`s" based on the cursor
  column, when the cursor selection would otherwise be ambiguous. For example, in:
  ```
  · foo
    · bar
      baz
    |
  ```
  where the cursor is at the `|`, we select the `tacticSeq` starting with `foo`, while if the
  cursor was indented to align with `baz` then we would select the `bar; baz` sequence instead.

* `range`: the cursor selection. We do not do much with range selections; if a range selection
  covers more than one tactic then we abort.

* `root`: the root syntax to process

The return value is either a selected tactic, or a selected point in a tactic sequence.
-/
partial def findTactic? (preferred : String.Pos → Bool) (range : String.Range)
    (root : Syntax) : Option FindTacticResult := do _ ← visit root; ← go [] root
where
  /-- Returns `none` if we should not visit this syntax at all, and `some false` if we only
  want to visit it in "extended" mode (where we include trailing characters). -/
  visit (stx : Syntax) (prev? : Option String.Pos := none) : Option Bool := do
    let left ← stx.getPos? true
    guard <| prev?.getD left ≤ range.start
    let .original (endPos := right) (trailing := trailing) .. := stx.getTailInfo | none
    guard <| right.byteIdx + trailing.bsize ≥ range.stop.byteIdx
    return left ≤ range.start && right ≥ range.stop

  /-- Merges the results of two `FindTacticResult`s. This just prefers the second (inner) one,
  unless the inner tactic is a dispreferred tactic sequence and the outer one is preferred.
  This is used to implement whitespace-sensitive selection of tactic sequences. -/
  merge : (r₁ : Option FindTacticResult) → (r₂ : FindTacticResult) → FindTacticResult
  | some r₁@(.tacticSeq (preferred := true) ..), .tacticSeq (preferred := false) .. => r₁
  | _, r₂ => r₂

  /-- Main recursion for `findTactic?`. This takes a `stack` context and a root syntax `stx`,
  and returns the best `FindTacticResult` it can find. It returns `none` (abort) if two or more
  results are found, and `some none` (none yet) if no results are found. -/
  go (stack : Syntax.Stack) (stx : Syntax) (prev? : Option String.Pos := none) :
      Option (Option FindTacticResult) := do
    if stx.getKind == ``Parser.Tactic.tacticSeq then
      -- TODO: this implementation is a bit too strict about the beginning of tacticSeqs.
      -- We would like to be able to parse
      -- · |
      --   foo
      -- (where `|` is the cursor position) as an insertion into the sequence containing foo
      -- at index 0, but we currently use the start of the tacticSeq, which is the foo token,
      -- as the earliest possible location that will be associated to the sequence.
      let bracket := stx[0].getKind == ``Parser.Tactic.tacticSeqBracketed
      let argIdx := if bracket then 1 else 0
      let (stack, stx) := ((stx[0], argIdx) :: (stx, 0) :: stack, stx[0][argIdx])
      let mainRes := stx[0].getPos?.map fun pos =>
        let i := Id.run do
          for i in [0:stx.getNumArgs] do
            if let some pos' := stx[2*i].getPos? then
              if range.stop < pos' then
                return i
          (stx.getNumArgs + 1) / 2
        .tacticSeq (bracket || preferred pos) i ((stx, 0) :: stack)
      let mut childRes := none
      for i in [0:stx.getNumArgs:2] do
        if let some inner := visit stx[i] then
          let stack := (stx, i) :: stack
          if let some child := (← go stack stx[i]) <|>
            (if inner then some (.tactic ((stx[i], 0) :: stack)) else none)
          then
            if childRes.isSome then failure
            childRes := merge mainRes child
      return childRes <|> mainRes
    else
      let mut childRes := none
      let mut prev? := prev?
      for i in [0:stx.getNumArgs] do
        if let some _ := visit stx[i] prev? then
          if let some child ← go ((stx, i) :: stack) stx[i] prev? then
            if childRes.isSome then failure
            childRes := child
        prev? := stx[i].getTailPos? true <|> prev?
      return childRes

/--
Returns the info tree corresponding to a syntax, using `kind` and `range` for identification.
(This is not foolproof, but it is a fairly accurate proxy for `Syntax` equality and a lot cheaper
than deep comparison.)
-/
partial def findInfoTree? (kind : SyntaxNodeKind) (tgtRange : String.Range)
  (ctx? : Option ContextInfo) (t : InfoTree)
  (f : ContextInfo → Info → Bool) (canonicalOnly := false) :
    Option (ContextInfo × InfoTree) :=
  match t with
  | .context ctx t => findInfoTree? kind tgtRange (ctx.mergeIntoOuter? ctx?) t f canonicalOnly
  | node@(.node i ts) => do
    if let some ctx := ctx? then
      if let some range := i.stx.getRange? canonicalOnly then
        -- FIXME: info tree needs to be organized better so that this works
        -- guard <| range.includes tgtRange
        if i.stx.getKind == kind && range == tgtRange && f ctx i then
          return (ctx, node)
    for t in ts do
      if let some res := findInfoTree? kind tgtRange (i.updateContext? ctx?) t f canonicalOnly then
        return res
    none
  | _ => none

/-- A code action which calls `@[tactic_code_action]` code actions. -/
@[code_action_provider] def tacticCodeActionProvider : CodeActionProvider := fun params snap => do
  let doc ← readDoc
  let startPos := doc.meta.text.lspPosToUtf8Pos params.range.start
  let endPos := doc.meta.text.lspPosToUtf8Pos params.range.end
  let pointerCol :=
    if params.range.start.line == params.range.end.line then
      max params.range.start.character params.range.end.character
    else 0
  let some result := findTactic?
    (fun pos => (doc.meta.text.utf8PosToLspPos pos).character ≤ pointerCol)
    ⟨startPos, endPos⟩ snap.stx | return #[]
  let tgtTac := match result with
    | .tactic (tac :: _)
    | .tacticSeq _ _ (_ :: tac :: _) => tac.1
    | _ => unreachable!
  let tgtRange := tgtTac.getRange?.get!
  have info := findInfoTree? tgtTac.getKind tgtRange none snap.infoTree (canonicalOnly := true)
    fun _ info => info matches .ofTacticInfo _
  let some (ctx, node@(.node (.ofTacticInfo info) _)) := info | return #[]
  let mut out := #[]
  match result with
  | .tactic stk@((tac, _) :: _) => do
    let ctx := { ctx with mctx := info.mctxBefore }
    let actions := (tacticCodeActionExt.getState snap.env).2
    if let some arr := actions.onTactic.find? tac.getKind then
      for act in arr do
        try out := out ++ (← act params snap ctx stk node) catch _ => pure ()
    for act in actions.onAnyTactic do
      try out := out ++ (← act params snap ctx stk node) catch _ => pure ()
  | .tacticSeq _ i stk@((seq, _) :: _) =>
    let (ctx, goals) ← if 2*i < seq.getNumArgs then
      let stx := seq[2*i]
      let some stxRange := stx.getRange? | return #[]
      let some (ctx, .node (.ofTacticInfo info') _) :=
          findInfoTree? stx.getKind stxRange ctx node fun _ info => (info matches .ofTacticInfo _)
        | return #[]
      pure ({ ctx with mctx := info'.mctxBefore }, info'.goalsBefore)
    else
      pure ({ ctx with mctx := info.mctxAfter }, info.goalsAfter)
    for act in (tacticSeqCodeActionExt.getState snap.env).2 do
      try out := out ++ (← act params snap ctx i stk goals) catch _ => pure ()
  | _ => unreachable!
  pure out
