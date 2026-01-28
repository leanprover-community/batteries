/-
Copyright (c) 2026 Chad Sharp. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chad Sharp
-/
module

@[expose] public section

/-- Boolean '<' is well founded -/
def Bool.lt_wfRel : WellFoundedRelation Bool where
  rel := (· < ·)
  wf := ⟨fun
    | false => ⟨false, nofun⟩
    | true => ⟨true, fun | false, _ => ⟨false, nofun⟩⟩⟩

/-- Boolean '>' is well founded -/
def Bool.gt_wfRel : WellFoundedRelation Bool where
  rel := (· > ·)
  wf := ⟨fun
    | true => ⟨true, nofun⟩
    | false => ⟨false, fun | true, _ => ⟨true, nofun⟩⟩⟩
