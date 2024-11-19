import Batteries -- needs `nightly-testing`

/-- Add `n` random even numbers to `k`. -/
def addRandomEvens (n : Nat) (k : Nat) : IO Nat := do
  let mut r := k
  for _ in List.range n do
    r := r + 2 * (← IO.rand 0 37)
  pure r

/-- The result has the same parity as the input. -/
theorem addRandomEvens_spec (n k) : SatisfiesM (fun r => r % 2 = k % 2) (addRandomEvens n k) := by
  simp [addRandomEvens]
  apply List.satisfiesM_foldlM
  · rfl
  · intros b w a m
    apply SatisfiesM.bind_pre
    simp_all [SatisfiesM_EStateM_eq, EStateM.run]

/--
Add `n` random even numbers to `k`,
returning the result and a proof it has the same parity as `k`.
-/
def addRandomEvens' (n : Nat) (k : Nat) : IO { r : Nat // r % 2 = k % 2 } := do
  satisfying (addRandomEvens_spec n k)

-- @[simp] theorem bind_map_subtype [Monad m] [LawfulMonad m] {p : α → Prop} (f : m { x // p x }) (g : α → m β) :
--     (do let r ← Subtype.val <$> f; g r) = (do let r' ← f; g r'.1) := by
--   simp

def program (n : Nat) (k : Nat) : IO Nat := do
  let r₁ ← addRandomEvens n k
  let r₂ ← addRandomEvens n k
  return r₁ + r₂

theorem program_spec (n k) : SatisfiesM (fun r => r % 2 = 0) (program n k) := by
  -- unfold program
  rw [program]
  -- apply the spec for addRandomEvens
  obtain ⟨r₁, h₁⟩ := addRandomEvens_spec n k
  simp [← h₁]
  -- now deal with `SatisfiesM`, fairly mechanically
  apply SatisfiesM.bind_pre
  apply SatisfiesM.of_true
  rintro ⟨x, hx⟩
  apply SatisfiesM.map_pre
  apply SatisfiesM.of_true
  rintro ⟨y, hx⟩
  -- finally, an honest goal:
  dsimp
  omega

abbrev M := StateM Nat

def count : M Nat := modifyGet (fun n => (n, n + 1))

example : SatisfiesM (fun r => r.2 = r.1 + 3) (do
    let r₁ ← count
    let r₂ ← count
    let r₃ ← count
    let r₄ ← count
    pure (r₁, r₄)) := by
  -- This actually works by `simp [count]`,
  -- but we want to write some preliminary theorems about `count`,
  -- and then reason compositionally.
  sorry

def countN (n : Nat) : M Nat := modifyGet (fun i => (i, i + n))

@[simp] theorem count_eq_countN : count = countN 1 := by
  apply StateT.ext
  intro s
  simp [count, countN]

@[simp] theorem bind_countN_bind_countN (f : Nat → Nat → M α) :
    (bind (countN n₁) fun r₁ => bind (countN n₂) fun r₂ => f r₁ r₂) = bind (countN (n₁ + n₂)) fun r => f r (r + n₁) := by
  apply StateT.ext
  intro s
  simp [count, countN, Nat.add_assoc]

@[simp] theorem bind_countN_map_countN (f : Nat → Nat → α) :
    (bind (countN n₁) fun r₁ => f r₁ <$> countN n₂) = (fun r₁ => f r₁ (r₁ + n₁)) <$> countN (n₁ + n₂) := by
  apply StateT.ext
  intro s
  simp [countN, Nat.add_assoc]

attribute [-simp] SatisfiesM_StateT_eq

set_option linter.unusedVariables false

example : SatisfiesM (fun r => r.2 = r.1 + 3) (do
    let r₁ ← count
    let r₂ ← count
    let r₃ ← count
    let r₄ ← count
    pure (r₁, r₄)) := by
  -- We could prove this just with `simp [count]`.
  -- Instead, we're going to treat `count` as a block box now,
  -- and only use `count_spec` compositionally!
  simp
  apply SatisfiesM.map_pre
  apply SatisfiesM.of_true
  intro a
  omega

/-- Dependent variant of `bind_countN_map_countN`. -/
@[simp] theorem bind_countN_map_countN' (f : Nat → Nat → α) (n₂ : Nat → Nat) :
    (bind (countN n₁) fun r₁ => f r₁ <$> countN (n₂ r₁)) =
      (do (fun r₁ => f r₁ (r₁ + n₁)) <$> countN (n₁ + n₂ (← get))) := by
  apply StateT.ext
  intro s
  simp [countN, Nat.add_assoc]

example : SatisfiesM (fun r => r.2 = r.1 + 3) (do
    let r₁ ← count
    let r₂ ← count
    let x := r₁ + 1 -- some spurious data
    let r₃ ← count
    let r₄ ← count
    let y ← countN x -- do some spurious operations afterwards
    pure (r₁, r₄)) := by
  simp
  apply SatisfiesM.bind_pre
  apply SatisfiesM.of_true
  intro s
  apply SatisfiesM.map_pre
  apply SatisfiesM.of_true
  intro a
  omega
