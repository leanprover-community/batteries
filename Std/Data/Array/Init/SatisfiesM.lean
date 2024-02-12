import Std.Data.Array.Init.Lemmas
import Std.Classes.LawfulMonad

namespace Array

theorem SatisfiesM_foldlM [Monad m] [LawfulMonad m]
    {as : Array α} (motive : Nat → β → Prop) {init : β} (h0 : motive 0 init) {f : β → α → m β}
    (hf : ∀ i : Fin as.size, ∀ b, motive i.1 b → SatisfiesM (motive (i.1 + 1)) (f b as[i])) :
    SatisfiesM (motive as.size) (as.foldlM f init) := by
  let rec go {i j b} (h₁ : j ≤ as.size) (h₂ : as.size ≤ i + j) (H : motive j b) :
    SatisfiesM (motive as.size) (foldlM.loop f as as.size (Nat.le_refl _) i j b) := by
    unfold foldlM.loop; split
    · next hj =>
      split
      · cases Nat.not_le_of_gt (by simp [hj]) h₂
      · exact (hf ⟨j, hj⟩ b H).bind fun _ => go hj (by rwa [Nat.succ_add] at h₂)
    · next hj => exact Nat.le_antisymm h₁ (Nat.ge_of_not_lt hj) ▸ .pure H
  simp [foldlM]; exact go (Nat.zero_le _) (Nat.le_refl _) h0

theorem foldl_induction
    {as : Array α} (motive : Nat → β → Prop) {init : β} (h0 : motive 0 init) {f : β → α → β}
    (hf : ∀ i : Fin as.size, ∀ b, motive i.1 b → motive (i.1 + 1) (f b as[i])) :
    motive as.size (as.foldl f init) := by
  have := SatisfiesM_foldlM (m := Id) (as := as) (f := f) motive h0
  simp [SatisfiesM_Id_eq] at this
  exact this hf

theorem SatisfiesM_mapM [Monad m] [LawfulMonad m] (as : Array α) (f : α → m β)
    (motive : Nat → Prop) (h0 : motive 0)
    (p : Fin as.size → β → Prop)
    (hs : ∀ i, motive i.1 → SatisfiesM (p i · ∧ motive (i + 1)) (f as[i])) :
    SatisfiesM
      (fun arr => motive as.size ∧ ∃ eq : arr.size = as.size, ∀ i h, p ⟨i, h⟩ (arr[i]'(eq ▸ h)))
      (Array.mapM f as) := by
  rw [mapM_eq_foldlM]
  refine SatisfiesM_foldlM (m := m) (β := Array β)
    (motive := fun i arr => motive i ∧ arr.size = i ∧ ∀ i h2, p i (arr[i.1]'h2)) ?z ?s
    |>.imp fun ⟨h₁, eq, h₂⟩ => ⟨h₁, eq, fun _ _ => h₂ ..⟩
  · case z => exact ⟨h0, rfl, fun.⟩
  · case s =>
    intro ⟨i, hi⟩ arr ⟨ih₁, eq, ih₂⟩
    refine (hs _ ih₁).map fun ⟨h₁, h₂⟩ => ⟨h₂, by simp [eq], fun j hj => ?_⟩
    simp [get_push] at hj ⊢; split; {apply ih₂}
    cases j; cases (Nat.le_or_eq_of_le_succ hj).resolve_left ‹_›; cases eq; exact h₁

theorem SatisfiesM_mapM' [Monad m] [LawfulMonad m] (as : Array α) (f : α → m β)
    (p : Fin as.size → β → Prop)
    (hs : ∀ i, SatisfiesM (p i) (f as[i])) :
    SatisfiesM
      (fun arr => ∃ eq : arr.size = as.size, ∀ i h, p ⟨i, h⟩ (arr[i]'(eq ▸ h)))
      (Array.mapM f as) :=
  (SatisfiesM_mapM _ _ (fun _ => True) trivial _ (fun _ h => (hs _).imp (⟨·, h⟩))).imp (·.2)

theorem size_mapM [Monad m] [LawfulMonad m] (f : α → m β) (as : Array α) :
    SatisfiesM (fun arr => arr.size = as.size) (Array.mapM f as) :=
  (SatisfiesM_mapM' _ _ (fun _ _ => True) (fun _ => .trivial)).imp (·.1)

@[simp] theorem getElem_map (f : α → β) (arr : Array α) (i : Nat) (h) :
    ((arr.map f)[i]'h) = f (arr[i]'(size_map .. ▸ h)) := by
  have := SatisfiesM_mapM' (m := Id) arr f (fun i b => b = f (arr[i]))
  simp [SatisfiesM_Id_eq] at this
  exact this.2 i (size_map .. ▸ h)

theorem SatisfiesM_anyM [Monad m] [LawfulMonad m] (p : α → m Bool) (as : Array α) (start stop)
    (hstart : start ≤ min stop as.size) (tru : Prop) (fal : Nat → Prop) (h0 : fal start)
    (hp : ∀ i : Fin as.size, i.1 < stop → fal i.1 →
      SatisfiesM (bif · then tru else fal (i + 1)) (p as[i])) :
    SatisfiesM
      (fun res => bif res then tru else fal (min stop as.size))
      (anyM p as start stop) := by
  let rec go {stop j} (hj' : j ≤ stop) (hstop : stop ≤ as.size) (h0 : fal j)
    (hp : ∀ i : Fin as.size, i.1 < stop → fal i.1 →
      SatisfiesM (bif · then tru else fal (i + 1)) (p as[i])) :
    SatisfiesM
      (fun res => bif res then tru else fal stop)
      (anyM.loop p as stop hstop j) := by
    unfold anyM.loop; split
    · next hj =>
      exact (hp ⟨j, Nat.lt_of_lt_of_le hj hstop⟩ hj h0).bind fun
        | true, h => .pure h
        | false, h => go hj hstop h hp
    · next hj => exact .pure <| Nat.le_antisymm hj' (Nat.ge_of_not_lt hj) ▸ h0
    termination_by stop - j
  simp only [Array.anyM_eq_anyM_loop]
  exact go hstart _ h0 fun i hi => hp i <| Nat.lt_of_lt_of_le hi <| Nat.min_le_left ..

theorem SatisfiesM_anyM_iff_exists [Monad m] [LawfulMonad m]
    (p : α → m Bool) (as : Array α) (start stop) (q : Fin as.size → Prop)
    (hp : ∀ i : Fin as.size, start ≤ i.1 → i.1 < stop → SatisfiesM (· = true ↔ q i) (p as[i])) :
    SatisfiesM
      (fun res => res = true ↔ ∃ i : Fin as.size, start ≤ i.1 ∧ i.1 < stop ∧ q i)
      (anyM p as start stop) := by
  cases Nat.le_total start (min stop as.size) with
  | inl hstart =>
    refine (SatisfiesM_anyM _ _ _ _ hstart
      (fal := fun j => start ≤ j ∧ ¬ ∃ i : Fin as.size, start ≤ i.1 ∧ i.1 < j ∧ q i)
      (tru := ∃ i : Fin as.size, start ≤ i.1 ∧ i.1 < stop ∧ q i) ?_ ?_).imp ?_
    · exact ⟨Nat.le_refl _, fun ⟨i, h₁, h₂, _⟩ => (Nat.not_le_of_gt h₂ h₁).elim⟩
    · refine fun i h₂ ⟨h₁, h₃⟩ => (hp _ h₁ h₂).imp fun hq => ?_
      unfold cond; split <;> simp at hq
      · exact ⟨_, h₁, h₂, hq⟩
      · refine ⟨Nat.le_succ_of_le h₁, h₃.imp fun ⟨j, h₃, h₄, h₅⟩ => ⟨j, h₃, ?_, h₅⟩⟩
        refine Nat.lt_of_le_of_ne (Nat.le_of_lt_succ h₄) fun e => hq (Fin.eq_of_val_eq e ▸ h₅)
    · intro
      | true, h => simp only [true_iff]; exact h
      | false, h =>
        simp only [false_iff]
        exact h.2.imp fun ⟨j, h₁, h₂, hq⟩ => ⟨j, h₁, Nat.lt_min.2 ⟨h₂, j.2⟩, hq⟩
  | inr hstart =>
    rw [anyM_stop_le_start (h := hstart)]
    refine .pure ?_; simp [not_and]; intro j h₁ h₂
    cases Nat.not_lt.2 (Nat.le_trans hstart h₁) (Nat.lt_min.2 ⟨h₂, j.2⟩)

theorem any_iff_exists (p : α → Bool) (as : Array α) (start stop) :
    any as p start stop ↔ ∃ i : Fin as.size, start ≤ i.1 ∧ i.1 < stop ∧ p as[i] := by
  have := SatisfiesM_anyM_iff_exists (m := Id) p as start stop (p as[·]) (by simp)
  rwa [SatisfiesM_Id_eq] at this

theorem any_eq_true (p : α → Bool) (as : Array α) :
    any as p ↔ ∃ i : Fin as.size, p as[i] := by simp [any_iff_exists, Fin.isLt]

theorem any_def {p : α → Bool} (as : Array α) : as.any p = as.data.any p := by
  rw [Bool.eq_iff_iff, any_eq_true, List.any_eq_true]; simp only [List.mem_iff_get]
  exact ⟨fun ⟨i, h⟩ => ⟨_, ⟨i, rfl⟩, h⟩, fun ⟨_, ⟨i, rfl⟩, h⟩ => ⟨i, h⟩⟩

theorem contains_def [DecidableEq α] {a : α} {as : Array α} : as.contains a ↔ a ∈ as := by
  rw [mem_def, contains, any_def, List.any_eq_true]; simp [and_comm]

instance [DecidableEq α] (a : α) (as : Array α) : Decidable (a ∈ as) :=
  decidable_of_iff _ contains_def
