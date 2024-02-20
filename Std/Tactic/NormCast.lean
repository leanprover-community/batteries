/-
Copyright (c) 2019 Paul-Nicolas Madelaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul-Nicolas Madelaine, Robert Y. Lewis, Mario Carneiro, Gabriel Ebner
-/
import Lean.Elab.Tactic.Conv.Simp
import Std.Lean.Meta.Simp
import Std.Classes.Cast

/-!
# The `norm_cast` family of tactics.
-/

open Lean Meta Simp

namespace Int

/- These will be attached to definitions once norm_cast is in core. -/
attribute [norm_cast] Nat.cast_ofNat_Int
attribute [norm_cast] ofNat_add
attribute [norm_cast] ofNat_sub
attribute [norm_cast] ofNat_mul
attribute [norm_cast] ofNat_inj
attribute [norm_cast] ofNat_ediv
attribute [norm_cast] ofNat_emod
attribute [norm_cast] ofNat_dvd
attribute [norm_cast] ofNat_le
attribute [norm_cast] ofNat_lt
attribute [norm_cast] ofNat_pos

end Int
