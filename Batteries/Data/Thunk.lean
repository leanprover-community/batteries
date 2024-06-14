/-
Copyright (c) 2024 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE
Authors: François G. Dorais, et al.
-/

namespace Thunk

@[ext] protected theorem ext : {a b : Thunk α} → a.get = b.get → a = b
  | {..}, {..}, heq => congrArg _ <| funext fun _ => heq
