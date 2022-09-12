/-
Copyright (c) 2021 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Std.Classes.LawfulMonad

namespace Option

instance : LawfulMonad Option := LawfulMonad.mk'
  (id_map := fun x => Option.rec rfl (λ x => rfl) x)
  (pure_bind := fun x f => rfl)
  (bind_assoc := fun x f g => Option.rec rfl (fun x => rfl) x)
  (bind_pure_comp := fun f x => by cases x <;> rfl)

instance : LawfulApplicative Option := inferInstance
instance : LawfulFunctor Option := inferInstance
