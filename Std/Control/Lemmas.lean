/-
Copyright (c) 2023 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: François G. Dorais
-/

namespace ReaderT

attribute [ext] ReaderT.ext

@[simp] theorem run_failure [Monad m] [Alternative m] (ctx : ρ) :
    (failure : ReaderT ρ m α).run ctx = failure := rfl

@[simp] theorem run_orElse [Monad m] [Alternative m] (x y : ReaderT ρ m α) (ctx : ρ) :
    (x <|> y).run ctx = (x.run ctx <|> y.run ctx) := rfl

end ReaderT

namespace StateT

attribute [ext] StateT.ext

@[simp] theorem run_failure {α σ} [Monad m] [Alternative m] (s : σ) :
    (failure : StateT σ m α).run s = failure := rfl

@[simp] theorem run_orElse {α σ} [Monad m] [Alternative m] (x y : StateT σ m α) (s : σ) :
    (x <|> y).run s = (x.run s <|> y.run s) := rfl

end StateT
