/-
Copyright (c) 2022 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Ebner
-/
import Lean.Syntax

/-!
# Helper functions for working with typed syntaxes.
-/

namespace Lean

/--
Applies the given function to every subsyntax.

Like `Syntax.replaceM` but for typed syntax.
(Note there are no guarantees of type correctness here.)
-/
def TSyntax.replaceM [Monad M] (f : Syntax → M (Option Syntax)) (stx : TSyntax k) : M (TSyntax k) :=
  .mk <$> stx.1.replaceM f
