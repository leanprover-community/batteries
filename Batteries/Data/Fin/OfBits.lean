/-
Copyright (c) 2025 François G. Dorais. All rights reserved.
Released under Apache 2. license as described in the file LICENSE.
Authors: François G. Dorais
-/

import Batteries.Data.Nat.Lemmas

namespace Fin

/--
Construct an element of `Fin (2 ^ n)` from a sequence of bits (little endian).
-/
abbrev ofBits (f : Fin n → Bool) : Fin (2 ^ n) := ⟨Nat.ofBits f, Nat.ofBits_lt_two_pow f⟩

@[simp] theorem val_ofBits (f : Fin n → Bool) : (ofBits f).val = Nat.ofBits f := rfl
