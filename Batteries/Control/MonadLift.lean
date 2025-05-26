/-
Copyright (c) 2025 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
namespace Id

/-- The `pure` operation of a monad `m` can be seen as a lifting operation from `Id` to `m`. -/
instance [Pure m] : MonadLift Id m where
  monadLift := pure

/-- The lifting from `Id` to a lawful monad `m` induced by `pure` is lawful. -/
instance [Monad m] [LawfulMonad m] : LawfulMonadLift Id m where
  monadLift_pure := fun a => by simp [MonadLift.monadLift, pure]
  monadLift_bind := fun x f => by simp [MonadLift.monadLift, bind]

end Id
