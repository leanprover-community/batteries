/-
Copyright (c) 2023 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Mario Carneiro
-/
import Lean.Elab.InfoTree.Main

namespace Lean.Elab

/-- Like `InfoTree.foldInfo`, but also passes the whole node to `f` instead of just the head. -/
partial def InfoTree.foldInfo' (init : α) (f : ContextInfo → InfoTree → α → α) : InfoTree → α :=
  go none init
where
  /-- `foldInfo'.go` is like `foldInfo'` but with an additional outer context parameter `ctx?`. -/
  go ctx? a
  | context ctx t => go (ctx.mergeIntoOuter? ctx?) a t
  | t@(node i ts) =>
    let a := match ctx? with
      | none => a
      | some ctx => f ctx t a
    ts.foldl (init := a) (go <| i.updateContext? ctx?)
  | _ => a
