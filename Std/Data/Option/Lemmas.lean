/-
Copyright (c) 2021 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Std.Data.Option.Basic

namespace Option

theorem mem_iff {a : α} {b : Option α} : a ∈ b ↔ b = a := .rfl
