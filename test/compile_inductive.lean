import Lean
import Std

inductive Fin2 : Nat → Type
  | zero : Fin2 .zero
  | succ : Fin2 n → Fin2 n.succ

variable (α : Type u) in
inductive Vec : Nat → Type u
  | nil : Vec .zero
  | cons : α → Vec n → Vec n.succ

inductive Void
  | mk : (Unit → Unit → Void) → Void

#compile inductive Nat
#compile inductive List
#compile inductive Fin2
#compile inductive Vec
#compile inductive Void
#compile inductive PUnit
#compile inductive PEmpty
#compile inductive And
#compile inductive Or
#compile inductive False
#compile inductive Empty

example := @Nat.rec
example := @List.rec
example := @Fin2.rec
example := @Vec.rec
example := @Void.rec
example := @PUnit.rec
example := @PEmpty.rec

example := @Nat.recOn
example := @List.recOn
example := @Fin2.recOn
example := @Vec.recOn
example := @Void.recOn
example := @PUnit.recOn
example := @PEmpty.recOn
example := @And.recOn
example := @False.recOn
example := @Empty.recOn

example := @Nat.brecOn
example := @List.brecOn
example := @Fin2.brecOn
example := @Vec.brecOn
example := @Void.brecOn

open Lean

#eval Elab.Command.liftTermElabM do
  let recs := (← getEnv).constants.toList |>.filterMap λ | (n, .inductInfo _) => some n | _ => none
  let mut success := 0
  let mut skipped := 0
  for i in recs do
    try
      unless (← getConstInfoRec <| mkRecName i).numMotives == 1 do
        skipped := skipped + 1
        continue
      Std.Util.CompileInductive.compileInductive i
      success := success + 1
    catch
    | e => logError m!"[{i}] {e.toMessageData}"
  modifyThe Core.State λ s => { s with messages.msgs := s.messages.msgs.filter (·.severity != .warning) }
  modifyThe Core.State λ s => { s with messages := s.messages.errorsToWarnings }
  logInfo m!"{success} / {recs.length-skipped}"
