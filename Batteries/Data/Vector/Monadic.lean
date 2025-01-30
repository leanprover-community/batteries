/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import Batteries.Util.ProofWanted

namespace Vector

proof_wanted toArray_mapM [Monad m] [LawfulMonad m] (a : Vector α n) (f : α → m β) :
    toArray <$> a.mapM f = a.toArray.mapM f

-- proof_wanted toArray_mapIdxM [Monad m] [LawfulMonad m] (a : Vector α n) (f : Nat → α → m β) :
--     toArray <$> a.mapIdxM f = a.toArray.mapIdxM f

-- proof_wanted toArray_mapFinIdxM [Monad m] [LawfulMonad m] (a : Vector α n) (f : (i : Nat) → α → (h : i < n) → m β) :
--     toArray <$> a.mapFinIdxM f = a.toArray.mapFinIdxM (fun i a h => f i a (by simpa using h))

end Vector
