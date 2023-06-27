/-
Copyright (c) 2023 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Std.Tactic.OpenPrivate

namespace Std.Format

open private State State.mk State.out from Init.Data.Format.Basic in
/--
Renders a `Format` to a string. Similar to `Format.pretty`, but with additional options:
* `w`: the total width
* `indent`: the initial indentation
* `column`: the initial column for the first line
-/
def prettyExtra (f : Format) (w : Nat := defWidth) (indent : Nat := 0) (column := 0) : String :=
  let act : StateM State Unit := prettyM f w indent
  State.out <| act (State.mk "" column) |>.snd
