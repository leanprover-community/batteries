/-
Copyright (c) 2023 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: François G. Dorais, Eric Wieser
-/

namespace ReaderT

attribute [ext] ReaderT.ext

@[simp] theorem run_failure [Monad m] [Alternative m] (ctx : ρ) :
    (failure : ReaderT ρ m α).run ctx = failure := rfl

@[simp] theorem run_orElse [Monad m] [Alternative m] (x y : ReaderT ρ m α) (ctx : ρ) :
    (x <|> y).run ctx = (x.run ctx <|> y.run ctx) := rfl

@[simp] theorem run_throw [MonadExceptOf ε m] (e : ε) (ctx : ρ) :
    (throw e : ReaderT ρ m α).run ctx = throw e := rfl

@[simp] theorem run_throwThe [MonadExceptOf ε m] (e : ε) (ctx : ρ) :
    (throwThe ε e : ReaderT ρ m α).run ctx = throwThe ε e := rfl

@[simp] theorem run_tryCatch [MonadExceptOf ε m] (body : ReaderT ρ m α) (handler : ε → ReaderT ρ m α) (ctx : ρ) :
    (tryCatch body handler).run ctx = tryCatch (body.run ctx) (handler · |>.run ctx) := rfl
  
@[simp] theorem run_tryCatchThe [MonadExceptOf ε m] (body : ReaderT ρ m α) (handler : ε → ReaderT ρ m α) (ctx : ρ) :
    (tryCatchThe ε body handler).run ctx = tryCatchThe ε (body.run ctx) (handler · |>.run ctx) := rfl

end ReaderT

namespace StateT

attribute [ext] StateT.ext

@[simp] theorem run_failure {α σ} [Monad m] [Alternative m] (s : σ) :
    (failure : StateT σ m α).run s = failure := rfl

@[simp] theorem run_orElse {α σ} [Monad m] [Alternative m] (x y : StateT σ m α) (s : σ) :
    (x <|> y).run s = (x.run s <|> y.run s) := rfl

@[simp] theorem run_throw [Monad m] [MonadExceptOf ε m] (e : ε) (s : σ) :
    (throw e : StateT σ m α).run s = (do let a ← throw e; pure (a, s)) := rfl

@[simp] theorem run_throwThe [Monad m] [MonadExceptOf ε m] (e : ε) (s : σ) :
    (throwThe ε e : StateT σ m α).run s = (do let a ← throwThe ε e; pure (a, s)) := rfl

@[simp] theorem run_tryCatch [Monad m] [MonadExceptOf ε m] (body : StateT σ m α) (handler : ε → StateT σ m α) (s : σ) :
    (tryCatch body handler).run s = tryCatch (body.run s) (handler · |>.run s) := rfl
  
@[simp] theorem run_tryCatchThe [Monad m] [MonadExceptOf ε m] (body : StateT σ m α) (handler : ε → StateT σ m α) (s : σ) :
    (tryCatchThe ε body handler).run s = tryCatchThe ε (body.run s) (handler · |>.run s) := rfl

end StateT
