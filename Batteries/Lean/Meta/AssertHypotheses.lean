/-
Copyright (c) 2022 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

import Lean.Meta.Tactic.Assert

open Lean Lean.Meta

namespace Lean.Meta

/--
Description of a hypothesis for `Lean.MVarId.assertHypotheses'`.
-/
structure Hypothesis' extends Hypothesis where
  /-- The hypothesis' `BinderInfo` -/
  binderInfo : BinderInfo
  /-- The hypothesis' `LocalDeclKind` -/
  kind : LocalDeclKind

/--
Add the given hypotheses to the local context. This is a generalisation of
`Lean.MVarId.assertHypotheses` which lets you specify
-/
def _root_.Lean.MVarId.assertHypotheses' (mvarId : MVarId)
    (hs : Array Hypothesis') : MetaM (Array FVarId × MVarId) := do
  let (fvarIds, mvarId) ← mvarId.assertHypotheses $ hs.map (·.toHypothesis)
  mvarId.modifyLCtx fun lctx => Id.run do
    let mut lctx := lctx
    for h : i in [:hs.size] do
      let h := hs[i]
      if h.kind != .default then
        lctx := lctx.setKind fvarIds[i]! h.kind
      if h.binderInfo != .default then
        lctx := lctx.setBinderInfo fvarIds[i]! h.binderInfo
    pure lctx
  return (fvarIds, mvarId)

end Lean.Meta
