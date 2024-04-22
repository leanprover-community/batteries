/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Mario Carneiro, Markus Himmel
-/
import Std.Classes.BEq

universe v u

variable {α : Type u} {β : α → Type v}

namespace List

@[elab_as_elim]
theorem assoc_induction {motive : List (Σ a, β a) → Prop} (nil : motive [])
    (cons : (k : α) → (v : β k) → (tail : List (Σ a, β a)) → motive tail → motive (⟨k, v⟩ :: tail)) :
    (t : List (Σ a, β a)) → motive t
  | [] => nil
  | ⟨_, _⟩ :: _ => cons _ _ _ (assoc_induction nil cons _)

/-- `O(n)`. Returns the first entry in the list whose key is equal to `a`. -/
def findEntry? [BEq α] (a : α) : List (Σ a, β a) → Option (Σ a, β a)
  | [] => none
  | ⟨k, v⟩ :: es => bif k == a then some ⟨k, v⟩ else findEntry? a es

@[simp] theorem findEntry?_nil [BEq α] {a : α} : ([] : List (Σ a, β a)).findEntry? a = none := rfl
theorem findEntry?_cons [BEq α] {l : List (Σ a, β a)} {k a : α} {v : β k} :
    (⟨k, v⟩ :: l).findEntry? a = bif k == a then some ⟨k, v⟩ else l.findEntry? a := rfl

theorem findEntry?_cons_of_true [BEq α] {l : List (Σ a, β a)} {k a : α} {v : β k} (h : k == a) :
    (⟨k, v⟩ :: l).findEntry? a = some ⟨k, v⟩ := by
  simp [findEntry?, h]

theorem findEntry?_cons_of_false [BEq α] {l : List (Σ a, β a)} {k a : α} {v : β k} (h : (k == a) = false) :
    (⟨k, v⟩ :: l).findEntry? a = l.findEntry? a := by
  simp [findEntry?, h]

theorem findEntry?_eq_of_beq [BEq α] [EquivBEq α] {l : List (Σ a, β a)} {a a' : α} (h : a == a') :
    l.findEntry? a = l.findEntry? a' := by
  induction l using assoc_induction
  · simp
  · next k v l ih =>
    cases h' : k == a
    · have h₂ : (k == a') = false := BEq.neq_of_neq_of_beq h' h
      rw [findEntry?_cons_of_false h', findEntry?_cons_of_false h₂, ih]
    · rw [findEntry?_cons_of_true h', findEntry?_cons_of_true (BEq.trans h' h)]

section

variable {β : Type v}

def findValue? [BEq α] (a : α) : List ((_ : α) × β) → Option β
  | [] => none
  | ⟨k, v⟩ :: l => bif k == a then some v else l.findValue? k



@[simp] theorem findValue?_nil [BEq α] {a : α} : ([] : List ((_ : α) × β)).findValue? a = none := rfl
theorem findValue?_cons [BEq α] {l : AssocList' α β} {k a : α} {v : β} :
    (l.cons k v).find? a = bif k == a then some v else l.find? a := rfl

theorem find?_cons_of_true [BEq α] {l : AssocList' α β} {k a : α} {v : β} (h : k == a) :
    (l.cons k v).find? a = some v := by
  simp [find?, h]

theorem find?_cons_of_false [BEq α] {l : AssocList' α β} {k a : α} {v : β} (h : (k == a) = false) :
    (l.cons k v).find? a = l.find? a := by
  simp [find?, h]

theorem find?_eq_findEntry? [BEq α] {l : AssocList' α β} {a : α} :
    l.find? a = (l.findEntry? a).map (·.2) := by
  induction l
  · simp
  · next k v es ih =>
    cases h : k == a
    · rw [findEntry?_cons_of_false h, find?_cons_of_false h, ih]
    · rw [findEntry?_cons_of_true h, find?_cons_of_true h, Option.map_some']

theorem find?_eq_of_beq [BEq α] [EquivBEq α] {l : AssocList' α β} {a a' : α} (h : a == a') :
    l.find? a = l.find? a' := by
  simp [find?_eq_findEntry?, findEntry?_eq_of_beq h]

end

def findKey? [BEq α] (a : α) : AssocList α β → Option α
  | nil => none
  | cons k _ es => bif k == a then some k else findKey? a es

@[simp] theorem findKey?_nil [BEq α] {a : α} : (nil : AssocList α β).findKey? a = none := rfl
theorem findKey?_cons [BEq α] {l : AssocList α β} {k a : α} {v : β k} :
    (l.cons k v).findKey? a = bif k == a then some k else l.findKey? a := rfl

theorem findKey?_cons_of_true [BEq α] {l : AssocList α β} {k a : α} {v : β k} (h : k == a) :
    (l.cons k v).findKey? a = some k := by
  simp [findKey?, h]

theorem findKey?_cons_of_false [BEq α] {l : AssocList α β} {k a : α} {v : β k} (h : (k == a) = false) :
    (l.cons k v).findKey? a = l.findKey? a := by
  simp [findKey?, h]

theorem findKey?_eq_findEntry? [BEq α] {l : AssocList α β} {a : α} :
    l.findKey? a = (l.findEntry? a).map (·.1) := by
  induction l
  · simp
  · next k v es ih =>
    cases h : k == a
    · rw [findEntry?_cons_of_false h, findKey?_cons_of_false h, ih]
    · rw [findEntry?_cons_of_true h, findKey?_cons_of_true h, Option.map_some']

theorem findKey?_eq_of_beq [BEq α] [EquivBEq α] {l : AssocList α β} {a a' : α} (h : a == a') :
    l.findKey? a = l.findKey? a' := by
  simp [findKey?_eq_findEntry?, findEntry?_eq_of_beq h]

def contains [BEq α] (a : α) : AssocList α β → Bool
  | nil => false
  | cons k _ l => k == a || l.contains a

@[simp] theorem contains_nil [BEq α] {a : α} : (nil : AssocList α β).contains a = false := rfl
@[simp] theorem contains_cons [BEq α] {l : AssocList α β} {k a : α} {v : β k} :
    (l.cons k v).contains a = (k == a || l.contains a) := rfl

theorem contains_cons_eq_false [BEq α] {l : AssocList α β} {k a : α} {v : β k} :
    ((l.cons k v).contains a = false) ↔ ((k == a) = false) ∧ (l.contains a = false) := by
  rw [Bool.eq_iff_iff]
  simp [contains_cons, not_or]

theorem contains_cons_eq_true [BEq α] {l : AssocList α β} {k a : α} {v : β k} :
    ((l.cons k v).contains a) ↔ (k == a) ∨ (l.contains a) := by
  rw [Bool.eq_iff_iff]
  simp [contains_cons]

theorem contains_cons_of_beq [BEq α] {l : AssocList α β} {k a : α} {v : β k} (h : k == a) :
    (l.cons k v).contains a := contains_cons_eq_true.2 <| Or.inl h

@[simp]
theorem contains_cons_self [BEq α] [EquivBEq α] {l : AssocList α β} {k : α} {v : β k} :
    (l.cons k v).contains k := contains_cons_of_beq BEq.refl

theorem contains_cons_of_contains [BEq α] {l : AssocList α β} {k a : α} {v : β k} (h : l.contains a) :
    (l.cons k v).contains a := contains_cons_eq_true.2 <| Or.inr h

theorem contains_of_contains_cons [BEq α] {l : AssocList α β} {k a : α} {v : β k} (h₁ : (l.cons k v).contains a)
    (h₂ : (k == a) = false) : l.contains a := by
  rcases (contains_cons_eq_true.1 h₁) with (h|h)
  · exact False.elim (Bool.eq_false_iff.1 h₂ h)
  · exact h

theorem contains_eq_isSome_findEntry? [BEq α] {l : AssocList α β} {a : α} :
    l.contains a = (l.findEntry? a).isSome := by
  induction l
  · simp
  · next k v l ih =>
    cases h : k == a
    · simp [findEntry?_cons_of_false h, h, ih]
    · simp [findEntry?_cons_of_true h, h]

theorem contains_eq_isSome_find? {β : Type v} [BEq α] {l : AssocList' α β} {a : α} :
    l.contains a = (l.find? a).isSome := by
  simp [contains_eq_isSome_findEntry?, find?_eq_findEntry?]

theorem contains_eq_isSome_findKey? [BEq α] {l : AssocList α β} {a : α} :
    l.contains a = (l.findKey? a).isSome := by
  simp [contains_eq_isSome_findEntry?, findKey?_eq_findEntry?]

theorem contains_eq_of_beq [BEq α] [EquivBEq α] {l : AssocList α β} {a b : α} (h : a == b) :
    l.contains a = l.contains b := by
  simp [contains_eq_isSome_findEntry?, findEntry?_eq_of_beq h]

theorem contains_of_beq [BEq α] [EquivBEq α] {l : AssocList α β} {a b : α} (hla : l.contains a) (hab : a == b) :
    l.contains b := by
  rwa [← contains_eq_of_beq hab]

def findEntry [BEq α] (l : AssocList α β) (a : α) (h : l.contains a) : Σ a, β a :=
  (l.findEntry? a).get <| contains_eq_isSome_findEntry?.symm.trans h

theorem findEntry?_eq_some_findEntry [BEq α] {l : AssocList α β} {a : α} (h : l.contains a) :
    l.findEntry? a = some (l.findEntry a h) := by
  simp [findEntry]

theorem findEntry_cons_of_beq [BEq α] {l : AssocList α β} {k a : α} {v : β k} (h : k == a) :
    (l.cons k v).findEntry a (contains_cons_of_beq h) = ⟨k, v⟩ := by
  simp [findEntry, findEntry?_cons_of_true h]

@[simp]
theorem findEntry_cons_self [BEq α] [EquivBEq α] {l : AssocList α β} {k : α} {v : β k} :
    (l.cons k v).findEntry k contains_cons_self = ⟨k, v⟩ :=
  findEntry_cons_of_beq BEq.refl

theorem findEntry_cons_of_false [BEq α] {l : AssocList α β} {k a : α} {v : β k} {h₁ : (l.cons k v).contains a}
    (h₂ : (k == a) = false) : (l.cons k v).findEntry a h₁ = l.findEntry a (contains_of_contains_cons h₁ h₂) := by
  simp [findEntry, findEntry?_cons_of_false h₂]

def findKey [BEq α] (l : AssocList α β) (a : α) (h : l.contains a) : α :=
  (l.findKey? a).get <| contains_eq_isSome_findKey?.symm.trans h

theorem findKey?_eq_some_findKey [BEq α] {l : AssocList α β} {a : α} (h : l.contains a) :
    l.findKey? a = some (l.findKey a h) := by
  simp [findKey]

theorem findKey_cons_of_beq [BEq α] {l : AssocList α β} {k a : α} {v : β k} (h : k == a) :
    (l.cons k v).findKey a (contains_cons_of_beq h) = k := by
  simp [findKey, findKey?_cons_of_true h]

@[simp]
theorem findKey_cons_self [BEq α] [EquivBEq α] {l : AssocList α β} {k : α} {v : β k} :
    (l.cons k v).findKey k contains_cons_self = k :=
  findKey_cons_of_beq BEq.refl

theorem findKey_cons_of_false [BEq α] {l : AssocList α β} {k a : α} {v : β k} {h₁ : (l.cons k v).contains a}
    (h₂ : (k == a) = false) : (l.cons k v).findKey a h₁ = l.findKey a (contains_of_contains_cons h₁ h₂) := by
  simp [findKey, findKey?_cons_of_false h₂]

theorem findKey_beq [BEq α] {l : AssocList α β} {a : α} {h : l.contains a} : l.findKey a h == a := by
  induction l
  · simp at h
  · next k v t ih =>
    cases h' : k == a
    · rw [findKey_cons_of_false h']
      exact @ih (contains_of_contains_cons h h')
    · rwa [findKey_cons_of_beq h']

section

variable {β : Type v}

def find [BEq α] (l : AssocList' α β) (a : α) (h : l.contains a) : β :=
  (l.find? a).get <| contains_eq_isSome_find?.symm.trans h

theorem find?_eq_some_find [BEq α] {l : AssocList' α β} {a : α} (h : l.contains a) :
    l.find? a = some (l.find a h) := by
  simp [find]

theorem find_cons_of_beq [BEq α] {l : AssocList' α β} {k a : α} {v : β} (h : k == a) :
    (l.cons k v).find a (contains_cons_of_beq h) = v := by
  simp [find, find?_cons_of_true h]

@[simp]
theorem find_cons_self [BEq α] [EquivBEq α] {l : AssocList' α β} {k : α} {v : β} :
    (l.cons k v).find k contains_cons_self = v :=
  find_cons_of_beq BEq.refl

theorem find_cons_of_false [BEq α] {l : AssocList' α β} {k a : α} {v : β} {h₁ : (l.cons k v).contains a}
    (h₂ : (k == a) = false) : (l.cons k v).find a h₁ = l.find a (contains_of_contains_cons h₁ h₂) := by
  simp [find, find?_cons_of_false h₂]

end

def replace [BEq α] (a : α) (b : β a) : AssocList α β → AssocList α β
  | nil => nil
  | cons k v l => bif k == a then cons a b l else cons k v (replace a b l)

@[simp] theorem replace_nil [BEq α] {a : α} {b : β a} : nil.replace a b = nil := rfl
theorem replace_cons [BEq α] {l : AssocList α β} {k a : α} {v : β k} {b : β a} :
    (l.cons k v).replace a b = bif k == a then l.cons a b else (l.replace a b).cons k v := rfl

theorem replace_cons_of_true [BEq α] {l : AssocList α β} {k a : α} {v : β k} {b : β a} (h : k == a) :
    (l.cons k v).replace a b = l.cons a b := by
  simp [replace, h]

theorem replace_cons_of_false [BEq α] {l : AssocList α β} {k a : α} {v : β k} {b : β a} (h : (k == a) = false) :
    (l.cons k v).replace a b = (l.replace a b).cons k v := by
  simp [replace, h]

theorem replace_of_contains_eq_false [BEq α] {l : AssocList α β} {a : α} {b : β a} (h : l.contains a = false) :
    l.replace a b = l := by
  induction l
  · simp
  · next k v l ih =>
    rw [contains_cons_eq_false] at h
    rw [replace_cons_of_false h.1, ih h.2]

theorem findEntry?_replace_of_contains_eq_false [BEq α] {l : AssocList α β} {k a : α} {b : β a}
    (hl : l.contains a = false) : (l.replace a b).findEntry? k = l.findEntry? k := by
  rw [replace_of_contains_eq_false hl]

theorem findEntry?_replace_of_false [BEq α] [EquivBEq α] {l : AssocList α β} {k a : α} {b : β a}
    (h : (k == a) = false) : (l.replace a b).findEntry? k = l.findEntry? k := by
  induction l
  · simp
  · next k' v' l ih =>
    cases h' : k' == a
    · rw [replace_cons_of_false h', findEntry?_cons, findEntry?_cons, ih]
    · rw [replace_cons_of_true h']
      have hk : (k' == k) = false := BEq.neq_of_beq_of_neq h' (BEq.symm_false h)
      simp [findEntry?_cons_of_false (BEq.symm_false h), findEntry?_cons_of_false hk]

theorem findEntry?_replace_of_true [BEq α] [EquivBEq α] {l : AssocList α β} {k a : α} {b : β a} (hl : l.contains a = true)
    (h : k == a) : (l.replace a b).findEntry? k = some ⟨a, b⟩ := by
  induction l
  · simp at hl
  · next k' v' l ih =>
    cases hk'a : k' == a
    · rw [replace_cons_of_false hk'a]
      have hk'k : (k' == k) = false := BEq.neq_of_neq_of_beq hk'a (BEq.symm h)
      rw [findEntry?_cons_of_false hk'k]
      exact ih (contains_of_contains_cons hl hk'a)
    · rw [replace_cons_of_true hk'a, findEntry?_cons_of_true (BEq.symm h)]

section

variable {β : Type v}

theorem find?_replace_of_contains_eq_false [BEq α] {l : AssocList' α β} {k a : α} {b : β}
    (hl : l.contains a = false) : (l.replace a b).find? k = l.find? k := by
  simp [find?_eq_findEntry?, findEntry?_replace_of_contains_eq_false hl]

theorem find?_replace_of_false [BEq α] [EquivBEq α] {l : AssocList' α β} {k a : α} {b : β}
    (h : (k == a) = false) : (l.replace a b).find? k = l.find? k := by
  simp [find?_eq_findEntry?, findEntry?_replace_of_false h]

theorem find?_replace_of_true [BEq α] [EquivBEq α] {l : AssocList' α β} {k a : α} {b : β}
    (hl : l.contains a = true) (h : k == a) : (l.replace a b).find? k = some b := by
  simp [find?_eq_findEntry?, findEntry?_replace_of_true hl h]

end

theorem findKey?_replace_of_contains_eq_false [BEq α] {l : AssocList α β} {k a : α} {b : β a}
    (hl : l.contains a = false) : (l.replace a b).findKey? k = l.findKey? k := by
  simp [findKey?_eq_findEntry?, findEntry?_replace_of_contains_eq_false hl]

theorem findKey?_replace_of_false [BEq α] [EquivBEq α] {l : AssocList α β} {k a : α} {b : β a}
    (h : (k == a) = false) : (l.replace a b).findKey? k = l.findKey? k := by
  simp [findKey?_eq_findEntry?, findEntry?_replace_of_false h]

theorem findKey?_replace_of_true [BEq α] [EquivBEq α] {l : AssocList α β} {k a : α} {b : β a}
    (hl : l.contains a = true) (h : (k == a)) : (l.replace a b).findKey? k = some a := by
  simp [findKey?_eq_findEntry?, findEntry?_replace_of_true hl h]

theorem findKey?_replace [BEq α] [EquivBEq α] {l : AssocList α β} {k a : α} {b : β a} :
    (l.replace a b).findKey? k = bif l.contains a && k == a then some a else l.findKey? k := by
  cases hl : l.contains a
  · simp [findKey?_replace_of_contains_eq_false hl]
  · cases h : k == a
    · simp [findKey?_replace_of_false h]
    · simp [findKey?_replace_of_true hl h]

@[simp]
theorem contains_replace [BEq α] [EquivBEq α] {l : AssocList α β} {k a : α} {b : β a} :
    (l.replace a b).contains k = l.contains k := by
  cases h : l.contains a && k == a
  · rw [contains_eq_isSome_findKey?, findKey?_replace, h, cond_false, contains_eq_isSome_findKey?]
  · rw [contains_eq_isSome_findKey?, findKey?_replace, h, cond_true, Option.isSome_some, Eq.comm]
    rw [Bool.and_eq_true] at h
    exact contains_of_beq h.1 (BEq.symm h.2)

def erase [BEq α] (a : α) : AssocList α β → AssocList α β
  | nil => nil
  | cons k v l => bif k == a then l else cons k v (l.erase a)

@[simp] theorem erase_nil [BEq α] {a : α} : (nil : AssocList α β).erase a = nil := rfl
theorem erase_cons [BEq α] {l : AssocList α β} {k a : α} {v : β k} :
    (l.cons k v).erase a = bif k == a then l else cons k v (l.erase a) := rfl

theorem erase_cons_of_beq [BEq α] {l : AssocList α β} {k a : α} {v : β k} (h : k == a) :
    (l.cons k v).erase a = l :=
  by simp [erase_cons, h]

@[simp]
theorem erase_cons_self [BEq α] [EquivBEq α] {l : AssocList α β} {k : α} {v : β k} :
    (l.cons k v).erase k = l :=
  erase_cons_of_beq BEq.refl

theorem erase_cons_of_false [BEq α] {l : AssocList α β} {k a : α} {v : β k} (h : (k == a) = false) :
    (l.cons k v).erase a = (l.erase a).cons k v := by
  simp [erase_cons, h]

-- TODO: erase+replace

/--
`O(n)`. Convert an `AssocList α β` to the list of keys in appearance order.
-/
def keys : AssocList α β → List α
  | nil => []
  | cons k _ l => k :: (keys l)

@[simp] theorem keys_nil : (nil : AssocList α β).keys = [] := rfl
@[simp] theorem keys_cons {l : AssocList α β} {k : α} {v : β k} : (l.cons k v).keys = k :: l.keys := rfl

theorem contains_eq_keys_contains [BEq α] [EquivBEq α] {l : AssocList α β} {a : α} :
    l.contains a = l.keys.contains a := by
  induction l
  · rfl
  · next k _ l ih =>
    simp [ih, BEq.comm]

/-- The well-formedness predicate for `AssocList` says that keys are pairwise distinct. -/
structure WF [BEq α] (l : AssocList α β) : Prop where
  distinct : l.keys.Pairwise fun a b => (a == b) = false

@[simp]
theorem WF_nil [BEq α] : (nil : AssocList α β).WF :=
  ⟨by simp⟩

open List

theorem WF_of_sublist_keys [BEq α] {l l' : AssocList α β} (h : l'.keys <+ l.keys) : l.WF → l'.WF :=
  fun ⟨h'⟩ => ⟨h'.sublist h⟩

theorem WF_of_keys_eq [BEq α] {l l' : AssocList α β} (h : l.keys = l'.keys) : l.WF → l'.WF :=
  WF_of_sublist_keys (h ▸ Sublist.refl _)

theorem contains_iff_exists [BEq α] [EquivBEq α] {l : AssocList α β} {a : α} :
    l.contains a ↔ ∃ a' ∈ l.keys, a == a' := by
  rw [contains_eq_keys_contains, List.contains_iff_exists_beq]

theorem contains_eq_false_iff_forall [BEq α] [EquivBEq α] {l : AssocList α β} {a : α} :
    (l.contains a) = false ↔ ∀ a' ∈ l.keys, (a == a') = false := by
  simp only [Bool.eq_false_iff, ne_eq, contains_iff_exists, not_exists, not_and]

@[simp]
theorem WF_cons_iff [BEq α] [EquivBEq α] {l : AssocList α β} {k : α} {v : β k} :
    (l.cons k v).WF ↔ l.WF ∧ (l.contains k) = false := by
  refine ⟨fun ⟨h⟩ => ?_, fun ⟨⟨h₁⟩, h₂⟩ => ⟨?_⟩⟩
  · rw [keys_cons, List.pairwise_cons] at h
    exact ⟨⟨h.2⟩, contains_eq_false_iff_forall.2 h.1⟩
  · rw [keys_cons, List.pairwise_cons, ← contains_eq_false_iff_forall]
    exact ⟨h₂, h₁⟩

theorem WF_cons [BEq α] [EquivBEq α] {l : AssocList α β} {k : α} {v : β k} (h : l.contains k = false) :
    l.WF → (l.cons k v).WF :=
  fun h' => WF_cons_iff.mpr ⟨h', h⟩

theorem WF_replace [BEq α] [EquivBEq α] {l : AssocList α β} {k : α} {v : β k} (h : l.WF) : (l.replace k v).WF := by
  induction l
  · simp
  · next k' v' l ih =>
    rw [WF_cons_iff] at h
    cases hk'k : k' == k
    · rw [replace_cons_of_false hk'k, WF_cons_iff]
      refine ⟨ih h.1, ?_⟩
      simpa using h.2
    · rw [replace_cons_of_true hk'k, WF_cons_iff]
      refine ⟨h.1, ?_⟩
      simpa [contains_eq_of_beq (BEq.symm hk'k)] using h.2

def insert [BEq α] (l : AssocList α β) (k : α) (v : β k) : AssocList α β :=
  bif l.contains k then l.replace k v else l.cons k v

theorem insert_of_contains [BEq α] {l : AssocList α β} {k : α} {v : β k} (h : l.contains k) :
    l.insert k v = l.replace k v := by
  simp [insert, h]

theorem insert_of_contains_eq_false [BEq α] {l : AssocList α β} {k : α} {v : β k} (h : l.contains k = false) :
    l.insert k v = l.cons k v := by
  simp [insert, h]

theorem WF_insert [BEq α] [EquivBEq α] {l : AssocList α β} {k : α} {v : β k} (h : l.WF) : (l.insert k v).WF := by
  cases h' : l.contains k
  · rw [insert_of_contains_eq_false h', WF_cons_iff]
    exact ⟨h, h'⟩
  · rw [insert_of_contains h']
    exact WF_replace h

section

variable {β : Type v}

theorem find?_insert_of_beq [BEq α] [EquivBEq α] {l : AssocList' α β} {k a : α} {v : β} (h : k == a) :
    (l.insert k v).find? a = some v := by
  cases h' : l.contains k
  · rw [insert_of_contains_eq_false h', find?_cons_of_true h]
  · rw [insert_of_contains h', find?_replace_of_true h' (BEq.symm h)]

theorem find?_insert_of_self [BEq α] [EquivBEq α] {l : AssocList' α β} {k : α} {v : β} :
    (l.insert k v).find? k = some v :=
  find?_insert_of_beq BEq.refl

theorem find?_insert_of_false [BEq α] [EquivBEq α] {l : AssocList' α β} {k a : α} {v : β} (h : (k == a) = false) :
    (l.insert k v).find? a = l.find? a := by
  cases h' : l.contains k
  · rw [insert_of_contains_eq_false h', find?_cons_of_false h]
  · rw [insert_of_contains h', find?_replace_of_false (BEq.symm_false h)]

-- TODO: would this be a reasonable simp lemma?
theorem find?_insert [BEq α] [EquivBEq α] {l : AssocList' α β} {k a : α} {v : β} :
    (l.insert k v).find? a = bif k == a then some v else l.find? a := by
  cases h : k == a
  · simp [find?_insert_of_false h, h]
  · simp [find?_insert_of_beq h, h]

end

-- TODO: Unify order in `bif k == a` vs. `bif a == k`.
theorem findKey?_insert_of_contains [BEq α] [EquivBEq α] {l : AssocList α β} {k a : α} {v : β k}
    (h : l.contains k) : (l.insert k v).findKey? a = bif k == a then some k else l.findKey? a := by
  simp [insert_of_contains h, findKey?_replace, h, BEq.comm]

theorem findKey?_insert_of_contains_eq_false [BEq α] [EquivBEq α] {l : AssocList α β} {k a : α} {v : β k}
    (hl : (l.contains k) = false) :
    (l.insert k v).findKey? a = bif k == a then some k else l.findKey? a := by
  simp [insert_of_contains_eq_false hl, findKey?_cons]

theorem findKey?_insert [BEq α] [EquivBEq α] {l : AssocList α β} {k a : α} {v : β k} :
    (l.insert k v).findKey? a = bif k == a then some k else l.findKey? a := by
  cases hl : l.contains k
  · simp [findKey?_insert_of_contains_eq_false hl, hl]
  · simp [findKey?_insert_of_contains hl]

-- TODO: results about findEntry?+insert

@[simp]
theorem contains_insert [BEq α] [EquivBEq α] {l : AssocList α β} {k a : α} {v : β k} :
    (l.insert k v).contains a = ((k == a) || l.contains a) := by
  rw [contains_eq_isSome_findKey?, contains_eq_isSome_findKey?, findKey?_insert]
  cases k == a
  · simp
  · simp

theorem contains_insert_of_beq [BEq α] [EquivBEq α] {l : AssocList α β} {k a : α} {v : β k} (h : k == a) :
    (l.insert k v).contains a := by
  simp [h]

@[simp]
theorem contains_insert_self [BEq α] [EquivBEq α] {l : AssocList α β} {k : α} {v : β k} :
    (l.insert k v).contains k :=
  contains_insert_of_beq BEq.refl

@[simp]
theorem keys_erase [BEq α] [EquivBEq α] {l : AssocList α β} {k : α} :
    (l.erase k).keys = l.keys.erase k := by
  induction l
  · rfl
  · next k' v' l ih =>
    simp only [erase_cons, keys_cons, List.erase_cons]
    cases k' == k
    · simp [ih]
    · simp [ih]

theorem WF_erase [BEq α] [EquivBEq α] {l : AssocList α β} {k : α} : l.WF → (l.erase k).WF := by
  apply WF_of_sublist_keys (by simpa using erase_sublist' _ _)

theorem findEntry?_erase_self [BEq α] [EquivBEq α] {l : AssocList α β} {k : α} (h : l.WF) :
    (l.erase k).findEntry? k = none := by
  induction l
  · simp
  · next k' v' t ih =>
    cases h' : k' == k
    · rw [erase_cons_of_false h', findEntry?_cons_of_false h']
      exact ih (WF_cons_iff.1 h).1
    · rw [erase_cons_of_beq h', ← Option.not_isSome_iff_eq_none, Bool.not_eq_true,
        ← contains_eq_isSome_findEntry?, ← contains_eq_of_beq h']
      exact (WF_cons_iff.1 h).2

theorem findEntry?_erase_of_beq [BEq α] [EquivBEq α] {l : AssocList α β} {k a : α} (hl : l.WF)
    (hka : k == a) : (l.erase k).findEntry? a = none := by
  rw [← findEntry?_eq_of_beq hka, findEntry?_erase_self hl]

theorem findEntry?_erase_of_false [BEq α] [EquivBEq α] {l : AssocList α β} {k a : α}
    (hka : (k == a) = false) : (l.erase k).findEntry? a = l.findEntry? a := by
  induction l
  · simp
  · next k' v' t ih =>
    cases h' : k' == k
    · rw [erase_cons_of_false h']
      cases h'' : k' == a
      · rw [findEntry?_cons_of_false h'', ih, findEntry?_cons_of_false h'']
      · rw [findEntry?_cons_of_true h'', findEntry?_cons_of_true h'']
    · rw [erase_cons_of_beq h']
      have hx : (k' == a) = false := BEq.neq_of_beq_of_neq h' hka
      rw [findEntry?_cons_of_false hx]

theorem findEntry?_erase [BEq α] [EquivBEq α] {l : AssocList α β} {k a : α} (hl : l.WF) :
    (l.erase k).findEntry? a = bif k == a then none else l.findEntry? a := by
  cases h : k == a
  · simp [findEntry?_erase_of_false h, h]
  · simp [findEntry?_erase_of_beq hl h, h]

section

variable {β : Type v}

theorem find?_erase_self [BEq α] [EquivBEq α] {l : AssocList' α β} {k : α} (h : l.WF) :
    (l.erase k).find? k = none := by
  simp [find?_eq_findEntry?, findEntry?_erase_self h]

theorem find?_erase_of_beq [BEq α] [EquivBEq α] {l : AssocList' α β} {k a : α} (hl : l.WF)
    (hka : k == a) : (l.erase k).find? a = none := by
  simp [find?_eq_findEntry?, findEntry?_erase_of_beq hl hka]

theorem find?_erase_of_false [BEq α] [EquivBEq α] {l : AssocList' α β} {k a : α}
    (hka : (k == a) = false) : (l.erase k).find? a = l.find? a := by
  simp [find?_eq_findEntry?, findEntry?_erase_of_false hka]

theorem find?_erase [BEq α] [EquivBEq α] {l : AssocList' α β} {k a : α} (hl : l.WF) :
    (l.erase k).find? a = bif k == a then none else l.find? a := by
  simp [find?_eq_findEntry?, findEntry?_erase hl, apply_bif (Option.map _)]

end

theorem findKey?_erase_self [BEq α] [EquivBEq α] {l : AssocList α β} {k : α} (h : l.WF) :
    (l.erase k).findKey? k = none := by
  simp [findKey?_eq_findEntry?, findEntry?_erase_self h]

theorem findKey?_erase_of_beq [BEq α] [EquivBEq α] {l : AssocList α β} {k a : α} (hl : l.WF)
    (hka : k == a) : (l.erase k).findKey? a = none := by
  simp [findKey?_eq_findEntry?, findEntry?_erase_of_beq hl hka]

theorem findKey?_erase_of_false [BEq α] [EquivBEq α] {l : AssocList α β} {k a : α}
    (hka : (k == a) = false) : (l.erase k).findKey? a = l.findKey? a := by
  simp [findKey?_eq_findEntry?, findEntry?_erase_of_false hka]

theorem findKey?_erase [BEq α] [EquivBEq α] {l : AssocList α β} {k a : α} (hl : l.WF) :
    (l.erase k).findKey? a = bif k == a then none else l.findKey? a := by
  simp [findKey?_eq_findEntry?, findEntry?_erase hl, apply_bif (Option.map _)]

theorem contains_erase_self [BEq α] [EquivBEq α] {l : AssocList α β} {k : α} (h : l.WF) :
    (l.erase k).contains k = false := by
  simp [contains_eq_isSome_findEntry?, findEntry?_erase_self h]

theorem contains_erase_of_beq [BEq α] [EquivBEq α] {l : AssocList α β} {k a : α} (hl : l.WF)
    (hka : k == a) : (l.erase k).contains a = false := by
  rw [← contains_eq_of_beq hka, contains_erase_self hl]

theorem contains_erase_of_false [BEq α] [EquivBEq α] {l : AssocList α β} {k a : α}
    (hka : (k == a) = false) : (l.erase k).contains a = l.contains a := by
  simp [contains_eq_isSome_findEntry?, findEntry?_erase_of_false hka]

theorem contains_erase [BEq α] [EquivBEq α] {l : AssocList α β} {k a : α} (hl : l.WF) :
    (l.erase k).contains a = bif k == a then false else l.contains a := by
  simp [contains_eq_isSome_findEntry?, findEntry?_erase hl, apply_bif Option.isSome]

-- TODO: Technically this should be true without assuming l.WF
theorem contains_of_contains_erase [BEq α] [EquivBEq α] {l : AssocList α β} {k a : α} (hl : l.WF)
    (h : (l.erase k).contains a) : l.contains a := by
  cases hka : k == a
  · rwa [contains_erase_of_false hka] at h
  · simp [contains_erase_of_beq hl hka] at h

-- TODO: results about combining modification operations

end List
