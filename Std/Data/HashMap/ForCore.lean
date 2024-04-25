import Std.Data.List.Lemmas

theorem List.contains_append [BEq α] {s t : List α} :
    (s ++ t).contains a = (s.contains a || t.contains a) := by
  induction s <;> simp_all [Bool.or_assoc]

def Option.or : Option α → Option α → Option α
  | o@(some _), _ => o
  | none, o => o

@[simp] theorem Option.or_some {a : α} {o : Option α} : Option.or (some a) o = some a := rfl
@[simp] theorem Option.none_or (o : Option α) : Option.or none o = o := rfl

theorem Option.or_eq_bif {o o' : Option α} : Option.or o o' = bif o.isSome then o else o' := by
  cases o <;> rfl

@[simp]
theorem Option.isSome_or {o o' : Option α} : (Option.or o o').isSome = (o.isSome || o'.isSome) := by
  cases o <;> rfl

@[simp]
theorem Option.isNone_or {o o' : Option α} : (Option.or o o').isNone = (o.isNone && o'.isNone) := by
  cases o <;> rfl

@[simp]
theorem Option.or_eq_none {o o' : Option α} : Option.or o o' = none ↔ o = none ∧ o' = none := by
  cases o <;> simp

theorem Option.or_eq_some {o o' : Option α} {a : α} :
    Option.or o o' = some a ↔ o = some a ∨ (o = none ∧ o' = some a) := by
  cases o <;> simp

theorem Option.or_assoc (o₁ o₂ o₃ : Option α) :
    Option.or (Option.or o₁ o₂) o₃ = Option.or o₁ (Option.or o₂ o₃) := by
  cases o₁ <;> cases o₂ <;> rfl
instance : Std.Associative (Option.or (α := α)) := ⟨Option.or_assoc⟩

@[simp]
theorem Option.or_none (o : Option α) : Option.or o none = o := by
  cases o <;> rfl
instance : Std.LawfulIdentity (Option.or (α := α)) none where
  left_id := Option.none_or
  right_id := Option.or_none

@[simp]
theorem Option.or_self (o : Option α) : Option.or o o = o := by
  cases o <;> rfl
instance : Std.IdempotentOp (Option.or (α := α)) := ⟨Option.or_self⟩

theorem Option.or_eq_orElse (o o' : Option α) : Option.or o o' = o.orElse (fun _ => o') := by
  cases o <;> rfl

theorem List.bind_eq_foldl (f : α → List β) (l : List α) :
      l.bind f = l.foldl (fun acc a => acc ++ f a) [] := by
  simpa using go []
  where
    go (l') : l' ++ l.bind f = l.foldl (fun acc a => acc ++ f a) l' := by
      induction l generalizing l'
      · simp
      · next h t ih =>
        rw [List.cons_bind, ← List.append_assoc, ih, List.foldl_cons]


section

open Std

variable (f : α → α → α) [Std.Associative f]

theorem foldl_assoc (l : List α) (a₁ a₂ : α) :
    l.foldl f (f a₁ a₂) = f a₁ (l.foldl f a₂) := by
  induction l generalizing a₂
  · simp
  · next h t ih =>
    skip
    rw [List.foldl_cons, List.foldl_cons, ← ih, Associative.assoc (op := f)]

variable (e : α) [Std.LawfulRightIdentity f e]

theorem foldl_ident (l : List α) (a : α) :
    l.foldl f a = f a (l.foldl f e) := by
  rw [← LawfulRightIdentity.right_id (op := f) a, foldl_assoc,
    LawfulRightIdentity.right_id (op := f)]

instance : Std.Associative (List.append (α := α)) := ⟨List.append_assoc⟩
instance : Std.LawfulIdentity (List.append (α := α)) [] where
  left_id := List.nil_append
  right_id := List.append_nil


end
