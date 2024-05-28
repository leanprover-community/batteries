/-
Copyright (c) 2023 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Lean.Data.Name

namespace Lean.Name

/--
Returns true if this a part of name that is internal or dynamically
generated so that it may easily be changed.

Generally, user code should not explicitly use internal names.
-/
def isInternalDetail : Name → Bool
  | .str p s     =>
    s.startsWith "_"
      || s.startsWith "match_"
      || s.startsWith "proof_"
      || p.isInternalOrNum
  | .num _ _     => true
  | p            => p.isInternalOrNum
