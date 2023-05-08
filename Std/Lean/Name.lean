/-
Copyright (c) 2023 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/

namespace Lean.Name

/-- Returns true if the name has any numeric components. -/
def hasNum : Name → Bool
  | .anonymous => false
  | .str p _ => p.hasNum
  | .num _ _ => true
