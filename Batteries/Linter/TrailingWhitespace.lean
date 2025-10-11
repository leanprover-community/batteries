import Lean.Elab.Command
import Lean.Linter.Util

/-!
#  The "trailingWhitespace" linter

The "trailingWhitespace" linter emits a warning whenever a line ends with a space or a file
does not end with a line break.
-/

open Lean Elab

namespace Batteries.Linter

/--
The "trailingWhitespace" linter emits a warning whenever a line ends with a space or a file
does not end with a line break.
-/
register_option linter.trailingWhitespace : Bool := {
  defValue := false
  descr := "enable the trailingWhitespace linter"
}

namespace TrailingWhitespace

@[inherit_doc Batteries.Linter.linter.trailingWhitespace]
def trailingWhitespaceLinter : Linter where run := withSetOptionIn fun stx => do
  unless Linter.getLinterValue linter.trailingWhitespace (← getOptions) do
    return
  if (← get).messages.hasErrors then
    return
  unless Parser.isTerminalCommand stx do return
  let fm ← getFileMap
  for lb in fm.positions do
    let last : Substring := { str := fm.source, startPos := ⟨lb.1 - 2⟩, stopPos := ⟨lb.1 - 1⟩ }
    if last.toString == " " then
      Linter.logLint linter.trailingWhitespace (.ofRange ⟨⟨lb.1 - 2⟩, ⟨lb.1 - 1⟩⟩)
        m!"Lines should not end with a space."
  let (backBack, back) := (fm.positions.pop.back, fm.positions.back)
  let rg : String.Range := ⟨back - ⟨1⟩, back⟩
  if backBack != back then
    Linter.logLint linter.trailingWhitespace (.ofRange rg) m!"Files should end with a line-break."

initialize addLinter trailingWhitespaceLinter

end TrailingWhitespace

end Batteries.Linter
