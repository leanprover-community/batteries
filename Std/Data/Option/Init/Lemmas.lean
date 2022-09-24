/-
Copyright (c) 2022 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/

namespace Option

/-!
# Bootstrapping theorems for Option

These are theorems used in the definitions of `Std.Data.List.Basic`.
New theorems should be added to `Std.Data.Option.Lemmas` if they are not needed by the bootstrap.
-/

@[simp] theorem getD_none : getD none a = a := rfl
@[simp] theorem getD_some : getD (some a) b = a := rfl

@[simp] theorem map_none' (f : α → β) : none.map f = none := rfl
@[simp] theorem map_some' (a) (f : α → β) : (some a).map f = some (f a) := rfl

@[simp] theorem none_bind (f : α → Option β) : none.bind f = none := rfl
@[simp] theorem some_bind (a) (f : α → Option β) : (some a).bind f = f a := rfl
