import Std.Classes.DecidableLT
import Std.Classes.DecidableLE
import Std.Tactic.GuardMsgs
import Std.Tactic.Omega

inductive Three where
  | one | two | three

inductive ThreeLT : (a b : Three) → Prop where
  | one : ThreeLT .one any
  | two : ThreeLT .two .three

instance : LT Three where
  lt := ThreeLT

instance : DecidableRel (@LT.lt Three _) := fun a b => by
  cases a <;> cases b <;>
  first
    | apply isTrue ; constructor
    | apply isFalse ; intro h ; cases h

abbrev ThreeLE (a b : Three) : Prop := ThreeLT a b ∨ a = b

instance : LE Three where
  le := ThreeLE

instance : DecidableRel (@LE.le Three _) := fun a b => by
    cases a <;> cases b <;>
  first
    | apply isTrue
      first
        | apply Or.inr
          rfl
        | apply Or.inl
          constructor
    | apply isFalse
      intro h
      cases h with | _ h =>
      cases h

def insertSorted [DecidableLT α] (arr : Array α) (i : Fin arr.size) : Array α :=
  match i with
  | ⟨0, _⟩ => arr
  | ⟨i' + 1, _⟩ =>
    have : i' < arr.size := by omega
    if arr[i'] < arr[i] then
      arr
    else
      insertSorted
        (arr.swap ⟨i', by assumption⟩ i)
        ⟨i', by simp [*]⟩

/-- info: #[1, 2, 3, 4, 5, 6] -/
#guard_msgs in #eval insertSorted #[1,2,4,5,3,6] ⟨4, by decide⟩

def insertSorted' [DecidableLE α] (arr : Array α) (i : Fin arr.size) : Array α :=
  match i with
  | ⟨0, _⟩ => arr
  | ⟨i' + 1, _⟩ =>
    have : i' < arr.size := by omega
    if arr[i'] ≤ arr[i] then
      arr
    else
      insertSorted'
        (arr.swap ⟨i', by assumption⟩ i)
        ⟨i', by simp [*]⟩

/-- info: #[1, 2, 3, 4, 5, 6] -/
#guard_msgs in #eval insertSorted' #[1,2,4,5,3,6] ⟨4, by decide⟩
