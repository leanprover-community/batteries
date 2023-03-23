import Std.Classes.LawfulMonad
import Lean.Linter

/-- Combination class of `Monad` and `Alternative` with a common `Applicative` component -/
class MonadAlternative (m : Type _ → Type _) extends Monad m, Alternative m

-- Missing docs in core
attribute [nolint docBlame] MonadAlternative.failure MonadAlternative.orElse

/-- Basic laws for `Alternative` -/
class LawfulAlternative (f : Type _ → Type _) [Alternative f] extends LawfulApplicative f : Prop where
  /-- Map failure is failure -/
  map_failure (g : α → β) : g <$> (failure : f α) = failure
  /-- Map distributes over `orElse` -/
  map_orElse (g : α → b) (x y : f α) : g <$> (x <|> y) = (g <$> x <|> g <$> y)
  /-- Failure is a left identity for `orElse`  -/
  failure_orElse (x : f α) : (failure <|> x) = x
  /-- Failure is a right identity for `orElse` -/
  orElse_failure (x : f α) : (x <|> failure) = x
  /-- `orElse` is associative -/
  orElse_assoc (x y z : f α) : (x <|> (y <|> z)) = ((x <|> y) <|> z)
  /-- `pure` always succeeds -/
  pure_orElse (x : α) (y : f α) : (pure x <|> y) = pure x

export LawfulAlternative (map_failure map_orElse failure_orElse orElse_failure orElse_assoc pure_orElse)

attribute [simp] map_failure failure_orElse pure_orElse

instance : LawfulAlternative Option where
  map_failure        := by intros; rfl
  map_orElse _ x _   := by cases x <;> rfl
  failure_orElse     := by intros; rfl
  orElse_failure x   := by cases x <;> rfl
  orElse_assoc x _ _ := by cases x <;> rfl
  pure_orElse        := by intros; rfl

namespace ReaderT

@[simp] theorem run_failure [Monad m] [Alternative m] (ctx : ρ) : (failure : ReaderT ρ m α).run ctx = failure := rfl

@[simp] theorem run_orElse [Monad m] [Alternative m] (x y : ReaderT ρ m α) (ctx : ρ) : (x <|> y).run ctx = (x.run ctx <|> y.run ctx) := rfl

instance [MonadAlternative m] [LawfulAlternative m] : LawfulAlternative (ReaderT ρ m) where
  map_failure    := by intros; apply ext; intros; simp
  map_orElse     := by intros; apply ext; intros; simp [map_orElse]
  failure_orElse := by intros; apply ext; intros; simp
  orElse_failure := by intros; apply ext; intros; simp [orElse_failure]
  orElse_assoc   := by intros; apply ext; intros; simp [orElse_assoc]
  pure_orElse    := by intros; apply ext; intros; simp

end ReaderT

instance [Monad m] [LawfulMonad m] : LawfulMonad (StateRefT' ω σ m) :=
  inferInstanceAs (LawfulMonad (ReaderT (ST.Ref ω σ) m))

instance [MonadAlternative m] [LawfulAlternative m] : LawfulAlternative (StateRefT' ω σ m) :=
  inferInstanceAs (LawfulAlternative (ReaderT (ST.Ref ω σ) m))

namespace StateT

@[simp] theorem run_failure {α σ : Type u} [Monad m] [Alternative m] (s : σ) : (failure : StateT σ m α).run s = failure := rfl

@[simp] theorem run_orElse {α σ : Type u} [Monad m] [Alternative m] (x y : StateT σ m α) (s : σ) : (x <|> y).run s = (x.run s <|> y.run s) := rfl

instance [MonadAlternative m] [LawfulMonad m] [LawfulAlternative m] : LawfulAlternative (StateT σ m) where
  map_failure    := by intros; apply ext; intros; simp
  map_orElse     := by intros; apply ext; intros; simp [map_orElse]
  failure_orElse := by intros; apply ext; intros; simp
  orElse_failure := by intros; apply ext; intros; simp [orElse_failure]
  orElse_assoc   := by intros; apply ext; intros; simp [orElse_assoc]
  pure_orElse    := by intros; apply ext; intros; simp

end StateT
