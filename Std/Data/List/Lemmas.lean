/-
Copyright (c) 2014 Parikshit Khanna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Parikshit Khanna, Jeremy Avigad, Leonardo de Moura, Floris van Doorn, Mario Carneiro
-/
import Std.Data.Nat.Lemmas
import Std.Data.List.Basic

namespace List

open Nat

/-! # Basic properties of Lists -/

attribute [simp] get! get? head? headD head tail! tail? tailD getLast! getLast?
  getLastD reverseAux eraseIdx isEmpty map map₂ join filterMap dropWhile find? findSome?
  replace elem lookup drop take takeWhile foldr zipWith unzip rangeAux enumFrom init
  intersperse isPrefixOf isEqv dropLast iota

theorem cons_ne_nil (a : α) (l : List α) : a :: l ≠ [] := fun.

theorem cons_ne_self (a : α) (l : List α) : a :: l ≠ l := mt (congrArg length) (Nat.succ_ne_self _)

theorem head_eq_of_cons_eq (H : h₁ :: t₁ = h₂ :: t₂) : h₁ = h₂ := (cons.inj H).1

theorem tail_eq_of_cons_eq (H : h₁ :: t₁ = h₂ :: t₂) : t₁ = t₂ := (cons.inj H).2

theorem cons_inj (a : α) {l l' : List α} : a :: l = a :: l' ↔ l = l' :=
  ⟨tail_eq_of_cons_eq, congrArg _⟩

theorem exists_cons_of_ne_nil : ∀ {l : List α}, l ≠ [] → ∃ b L, l = b :: L
  | c :: l', _ => ⟨c, l', rfl⟩

/-! ### length -/

theorem eq_nil_of_length_eq_zero (_ : length l = 0) : l = [] := match l with | [] => rfl

theorem ne_nil_of_length_eq_succ (_ : length l = succ n) : l ≠ [] := fun _ => nomatch l

theorem length_eq_zero : length l = 0 ↔ l = [] :=
  ⟨eq_nil_of_length_eq_zero, fun h => h ▸ rfl⟩

@[simp 1100] theorem length_singleton (a : α) : length [a] = 1 := rfl

theorem length_pos_of_mem {a : α} : ∀ {l : List α}, a ∈ l → 0 < length l
  | _::_, _ => Nat.zero_lt_succ _

theorem exists_mem_of_length_pos : ∀ {l : List α}, 0 < length l → ∃ a, a ∈ l
  | _::_, _ => ⟨_, .head ..⟩

theorem length_pos_iff_exists_mem {l : List α} : 0 < length l ↔ ∃ a, a ∈ l :=
  ⟨exists_mem_of_length_pos, fun ⟨_, h⟩ => length_pos_of_mem h⟩

theorem length_pos_iff_ne_nil {l : List α} : 0 < length l ↔ l ≠ [] :=
  Nat.pos_iff_ne_zero.trans (not_congr length_eq_zero)

theorem exists_mem_of_ne_nil (l : List α) (h : l ≠ []) : ∃ x, x ∈ l :=
  exists_mem_of_length_pos (length_pos_iff_ne_nil.2 h)

theorem length_eq_one {l : List α} : length l = 1 ↔ ∃ a, l = [a] :=
  ⟨fun h => match l, h with | [_], _ => ⟨_, rfl⟩, fun ⟨_, h⟩ => by simp [h]⟩

/-! ### mem -/

@[simp] theorem not_mem_nil (a : α) : ¬ a ∈ [] := fun.

theorem mem_nil_iff (a : α) : a ∈ ([] : List α) ↔ False := by simp

@[simp] theorem mem_cons : a ∈ (b :: l) ↔ a = b ∨ a ∈ l :=
  ⟨fun h => by cases h <;> simp [Membership.mem, *],
   fun | Or.inl rfl => by constructor | Or.inr h => by constructor; assumption⟩

theorem mem_cons_self (a : α) (l : List α) : a ∈ a :: l := .head ..

theorem mem_cons_of_mem (y : α) {a : α} {l : List α} : a ∈ l → a ∈ y :: l := .tail _

theorem mem_singleton_self (a : α) : a ∈ [a] := mem_cons_self _ _

theorem eq_of_mem_singleton : ∀ {a b : α}, a ∈ [b] → a = b
  | _, _, .head .. => rfl

@[simp 1100] theorem mem_singleton {a b : α} : a ∈ [b] ↔ a = b :=
  ⟨eq_of_mem_singleton, (by simp [·])⟩

theorem mem_of_mem_cons_of_mem : ∀ {a b : α} {l : List α}, a ∈ b :: l → b ∈ l → a ∈ l
  | _, _, _, .head .., h | _, _, _, .tail _ h, _ => h

theorem eq_or_ne_mem_of_mem {a b : α} {l : List α} (h' : a ∈ b :: l) : a = b ∨ (a ≠ b ∧ a ∈ l) :=
  (Classical.em _).imp_right fun h => ⟨h, (mem_cons.1 h').resolve_left h⟩

theorem ne_nil_of_mem {a : α} {l : List α} (h : a ∈ l) : l ≠ [] := by cases h <;> intro.

theorem mem_constructor : ∀ {a : α} {l : List α}, a ∈ l → ∃ s t : List α, l = s ++ a :: t
  | _, _, .head _ l => ⟨[], l, rfl⟩
  | _, _, .tail b hmem =>
    let ⟨s, t, h'⟩ := mem_constructor hmem; ⟨b::s, t, by rw [h', cons_append]⟩

/-! ### append -/

theorem append_eq_append : List.append l₁ l₂ = l₁ ++ l₂ := rfl

@[simp 1100] theorem singleton_append : [x] ++ l = x :: l := rfl

@[simp] theorem append_eq_nil : p ++ q = [] ↔ p = [] ∧ q = [] := by
  cases p <;> simp

theorem append_ne_nil_of_ne_nil_left (s t : List α) : s ≠ [] → s ++ t ≠ [] := by simp_all

theorem append_ne_nil_of_ne_nil_right (s t : List α) : t ≠ [] → s ++ t ≠ [] := by simp_all

@[simp] theorem nil_eq_append : [] = a ++ b ↔ a = [] ∧ b = [] := by
  rw [eq_comm, append_eq_nil]

theorem append_ne_nil_of_left_ne_nil (a b : List α) (h0 : a ≠ []) : a ++ b ≠ [] := by simp [*]

theorem append_eq_cons :
    a ++ b = x :: c ↔ (a = [] ∧ b = x :: c) ∨ (∃ a', a = x :: a' ∧ c = a' ++ b) := by
  cases a with simp | cons a as => ?_
  exact ⟨fun h => ⟨as, by simp [h]⟩, fun ⟨a', ⟨aeq, aseq⟩, h⟩ => ⟨aeq, by rw [aseq, h]⟩⟩

theorem cons_eq_append :
    x :: c = a ++ b ↔ (a = [] ∧ b = x :: c) ∨ (∃ a', a = x :: a' ∧ c = a' ++ b) := by
  rw [eq_comm, append_eq_cons]

theorem append_eq_append_iff {a b c d : List α} :
  a ++ b = c ++ d ↔ (∃ a', c = a ++ a' ∧ b = a' ++ d) ∨ ∃ c', a = c ++ c' ∧ d = c' ++ b := by
  induction a generalizing c with
  | nil => simp; exact (or_iff_left_of_imp fun ⟨_, ⟨e, rfl⟩, h⟩ => e ▸ h.symm).symm
  | cons a as ih => cases c <;> simp [eq_comm, and_assoc, ih, and_or_left]

theorem append_inj :
    ∀ {s₁ s₂ t₁ t₂ : List α}, s₁ ++ t₁ = s₂ ++ t₂ → length s₁ = length s₂ → s₁ = s₂ ∧ t₁ = t₂
  | [], [], t₁, t₂, h, _ => ⟨rfl, h⟩
  | a :: s₁, b :: s₂, t₁, t₂, h, hl => by
    simp [append_inj (cons.inj h).2 (Nat.succ.inj hl)] at h ⊢; exact h

theorem append_inj_right (h : s₁ ++ t₁ = s₂ ++ t₂) (hl : length s₁ = length s₂) : t₁ = t₂ :=
  (append_inj h hl).right

theorem append_inj_left (h : s₁ ++ t₁ = s₂ ++ t₂) (hl : length s₁ = length s₂) : s₁ = s₂ :=
  (append_inj h hl).left

theorem append_inj' (h : s₁ ++ t₁ = s₂ ++ t₂) (hl : length t₁ = length t₂) : s₁ = s₂ ∧ t₁ = t₂ :=
  append_inj h <| @Nat.add_right_cancel _ (length t₁) _ <| by
  let hap := congrArg length h; simp only [length_append, ← hl] at hap; exact hap

theorem append_inj_right' (h : s₁ ++ t₁ = s₂ ++ t₂) (hl : length t₁ = length t₂) : t₁ = t₂ :=
  (append_inj' h hl).right

theorem append_inj_left' (h : s₁ ++ t₁ = s₂ ++ t₂) (hl : length t₁ = length t₂) : s₁ = s₂ :=
  (append_inj' h hl).left

theorem append_right_inj {s t₁ t₂ : List α} (h : s ++ t₁ = s ++ t₂) : t₁ = t₂ :=
  append_inj_right h rfl

theorem append_left_inj {s₁ s₂ t : List α} (h : s₁ ++ t = s₂ ++ t) : s₁ = s₂ :=
  append_inj_left' h rfl

@[simp] theorem mem_append {a : α} {s t : List α} : a ∈ s ++ t ↔ a ∈ s ∨ a ∈ t := by
  induction s <;> simp_all [or_assoc]

theorem mem_append_eq (a : α) (s t : List α) : (a ∈ s ++ t) = (a ∈ s ∨ a ∈ t) :=
  propext mem_append

theorem mem_append_left {a : α} {l₁ : List α} (l₂ : List α) (h : a ∈ l₁) : a ∈ l₁ ++ l₂ :=
  mem_append.2 (Or.inl h)

theorem mem_append_right {a : α} (l₁ : List α) {l₂ : List α} (h : a ∈ l₂) : a ∈ l₁ ++ l₂ :=
  mem_append.2 (Or.inr h)

/-! ### map -/

theorem map_nil {f : α → β} : map f [] = [] := rfl

theorem map_cons (f : α → β) a l : map f (a :: l) = f a :: map f l := rfl

@[simp] theorem map_append (f : α → β) : ∀ l₁ l₂, map f (l₁ ++ l₂) = map f l₁ ++ map f l₂ := by
  intro l₁ <;> induction l₁ <;> intros <;> simp_all

theorem map_singleton (f : α → β) (a : α) : map f [a] = [f a] := rfl

@[simp] theorem map_id (l : List α) : map id l = l := by induction l <;> simp_all

@[simp] theorem map_map (g : β → γ) (f : α → β) (l : List α) :
  map g (map f l) = map (g ∘ f) l := by induction l <;> simp_all

theorem mem_map {f : α → β} : ∀ {l : List α}, b ∈ l.map f ↔ ∃ a, a ∈ l ∧ b = f a
  | [] => by simp
  | b :: l => by simp [mem_map (l := l), or_and_right, exists_or]

theorem mem_map_of_mem (f : α → β) (h : a ∈ l) : f a ∈ map f l := mem_map.2 ⟨_, h, rfl⟩

theorem exists_of_mem_map (h : b ∈ List.map f l) : ∃ a, a ∈ l ∧ b = f a := mem_map.1 h

theorem forall_mem_map_iff {f : α → β} {l : List α} {P : β → Prop} :
    (∀ i ∈ l.map f, P i) ↔ ∀ j ∈ l, P (f j) := by
  simp [mem_map]; exact ⟨fun H j h => H _ _ h rfl, fun H i x h e => e ▸ H _ h⟩

@[simp] theorem map_eq_nil {f : α → β} {l : List α} : List.map f l = [] ↔ l = [] := by
  constructor <;> exact fun _ => match l with | [] => rfl

@[simp] theorem length_map₂ (f : α → β → γ) l₁ :
  ∀ l₂, length (map₂ f l₁ l₂) = min (length l₁) (length l₂) := by
  induction l₁ <;> intro l₂ <;> cases l₂ <;>
    simp_all [add_one, min_succ_succ, Nat.zero_min, Nat.min_zero]

/-! ### join -/

theorem join_nil : join ([] : List (List α)) = [] := rfl

theorem join_cons : join (a :: l : List (List α)) = a ++ join l := rfl

theorem mem_join : ∀ {L : List (List α)}, a ∈ L.join ↔ ∃ l, l ∈ L ∧ a ∈ l
  | [] => by simp
  | b :: l => by simp [mem_join, or_and_right, exists_or]

theorem exists_of_mem_join : a ∈ join L → ∃ l, l ∈ L ∧ a ∈ l := mem_join.1

theorem mem_join_of_mem (lL : l ∈ L) (al : a ∈ l) : a ∈ join L := mem_join.2 ⟨l, lL, al⟩

/-! ### bind -/

@[simp] theorem nil_bind (f : α → List β) : List.bind [] f = [] := by simp [join, List.bind]

@[simp] theorem cons_bind x xs (f : α → List β) :
  List.bind (x :: xs) f = f x ++ List.bind xs f := by simp [join, List.bind]

@[simp] theorem append_bind xs ys (f : α → List β) :
  List.bind (xs ++ ys) f = List.bind xs f ++ List.bind ys f := by
  induction xs; {rfl}; simp_all [cons_bind, append_assoc]

theorem mem_bind {f : α → List β} {b} {l : List α} : b ∈ l.bind f ↔ ∃ a, a ∈ l ∧ b ∈ f a := by
  simp [List.bind, mem_map, mem_join]
  exact ⟨fun ⟨_, ⟨a, h₁, rfl⟩, h₂⟩ => ⟨a, h₁, h₂⟩, fun ⟨a, h₁, h₂⟩ => ⟨_, ⟨a, h₁, rfl⟩, h₂⟩⟩

theorem exists_of_mem_bind {b : β} {l : List α} {f : α → List β} :
    b ∈ List.bind l f → ∃ a, a ∈ l ∧ b ∈ f a := mem_bind.1

theorem mem_bind_of_mem {b : β} {l : List α} {f : α → List β} {a} (al : a ∈ l) (h : b ∈ f a) :
    b ∈ List.bind l f := mem_bind.2 ⟨a, al, h⟩

theorem bind_map (f : β → γ) (g : α → List β) :
    ∀ l : List α, List.map f (l.bind g) = l.bind fun a => (g a).map f
  | [] => rfl
  | a::l => by simp only [cons_bind, map_append, bind_map _ _ l]

/-! ### set-theoretic notation of Lists -/

@[simp] theorem empty_eq : (∅ : List α) = [] := rfl

/-! ### bounded quantifiers over Lists -/

theorem exists_mem_nil (p : α → Prop) : ¬∃ x ∈ @nil α, p x := fun.

theorem forall_mem_nil (p : α → Prop) : ∀ x ∈ @nil α, p x := fun.

theorem exists_mem_cons (p : α → Prop) (a : α) (l : List α) :
    (∃ x ∈ a :: l, p x) ↔ p a ∨ ∃ x ∈ l, p x := by simp

theorem forall_mem_cons (p : α → Prop) (a : α) (l : List α) :
    (∀ x ∈ a :: l, p x) ↔ p a ∧ ∀ x ∈ l, p x := by simp

theorem forall_mem_singleton {p : α → Prop} {a : α} : (∀ x ∈ [a], p x) ↔ p a := by
  simp only [mem_singleton, forall_eq]; rfl

theorem forall_mem_append {p : α → Prop} {l₁ l₂ : List α} :
    (∀ x ∈ l₁ ++ l₂, p x) ↔ (∀ x ∈ l₁, p x) ∧ (∀ x ∈ l₂, p x) := by
  simp only [mem_append, or_imp, forall_and]; rfl

/-! ### List subset -/

theorem subset_def {l₁ l₂ : List α} : l₁ ⊆ l₂ ↔ ∀ {a : α}, a ∈ l₁ → a ∈ l₂ := .rfl

@[simp] theorem nil_subset (l : List α) : [] ⊆ l := fun.

-- @[refl]
@[simp] theorem Subset.refl (l : List α) : l ⊆ l := fun _ i => i

-- @[trans]
theorem Subset.trans {l₁ l₂ l₃ : List α} (h₁ : l₁ ⊆ l₂) (h₂ : l₂ ⊆ l₃) : l₁ ⊆ l₃ :=
  fun _ i => h₂ (h₁ i)

@[simp] theorem subset_cons (a : α) (l : List α) : l ⊆ a :: l := fun _ => Mem.tail _

theorem subset_of_cons_subset {a : α} {l₁ l₂ : List α} : a :: l₁ ⊆ l₂ → l₁ ⊆ l₂ :=
  fun s _ i => s (mem_cons_of_mem _ i)

theorem subset_cons_of_subset (a : α) {l₁ l₂ : List α} : l₁ ⊆ l₂ → l₁ ⊆ a :: l₂ :=
  fun s _ i => .tail _ (s i)

theorem cons_subset_cons {l₁ l₂ : List α} (a : α) (s : l₁ ⊆ l₂) : a :: l₁ ⊆ a :: l₂ :=
  fun _ => by simp only [mem_cons]; exact Or.imp_right (@s _)

@[simp] theorem subset_append_left (l₁ l₂ : List α) : l₁ ⊆ l₁ ++ l₂ := fun _ => mem_append_left _

@[simp] theorem subset_append_right (l₁ l₂ : List α) : l₂ ⊆ l₁ ++ l₂ := fun _ => mem_append_right _

theorem subset_append_of_subset_left (l₂ : List α) : l ⊆ l₁ → l ⊆ l₁ ++ l₂ :=
fun s => Subset.trans s <| subset_append_left _ _

theorem subset_append_of_subset_right (l₁ : List α) : l ⊆ l₂ → l ⊆ l₁ ++ l₂ :=
fun s => Subset.trans s <| subset_append_right _ _

@[simp] theorem cons_subset : a :: l ⊆ m ↔ a ∈ m ∧ l ⊆ m := by
  simp only [subset_def, mem_cons, or_imp, forall_and, forall_eq]; rfl

@[simp] theorem append_subset {l₁ l₂ l : List α} :
    l₁ ++ l₂ ⊆ l ↔ l₁ ⊆ l ∧ l₂ ⊆ l := by simp [subset_def, or_imp, forall_and]

theorem subset_nil {l : List α} : l ⊆ [] ↔ l = [] :=
  ⟨fun h => match l with | [] => rfl | _::_ => nomatch h (.head ..), fun | rfl => Subset.refl _⟩

theorem eq_nil_iff_forall_not_mem {l : List α} : l = [] ↔ ∀ a, a ∉ l :=
  subset_nil.symm.trans <| by simp [subset_def]

theorem map_subset {l₁ l₂ : List α} (f : α → β) (H : l₁ ⊆ l₂) : map f l₁ ⊆ map f l₂ :=
  fun x => by simp only [mem_map]; exact .imp fun a => .imp_left (@H _)

/-! ### replicate -/

theorem replicate_succ (a : α) (n) : replicate (n+1) a = a :: replicate n a := rfl

theorem mem_replicate {a b : α} : ∀ {n}, b ∈ replicate n a ↔ n ≠ 0 ∧ b = a
  | 0 => by simp
  | n+1 => by simp [mem_replicate, Nat.succ_ne_zero]

theorem eq_of_mem_replicate {a b : α} {n} (h : b ∈ replicate n a) : b = a := (mem_replicate.1 h).2

/-! ### getLast -/

theorem getLast_cons {a : α} {l : List α} : ∀ (h₁ : a :: l ≠ nil) (h₂ : l ≠ nil),
  getLast (a :: l) h₁ = getLast l h₂ := by
  induction l <;> intros; {contradiction}; rfl

@[simp] theorem getLast_append {a : α} : ∀ (l : List α) h, getLast (l ++ [a]) h = a
  | [], _ => rfl
  | a::t, h => by
    simp [getLast_cons _ fun H => cons_ne_nil _ _ (append_eq_nil.1 H).2, getLast_append t]

theorem getLast_concat : (h : concat l a ≠ []) → getLast (concat l a) h = a :=
  concat_eq_append .. ▸ getLast_append _

/-! ### nth element -/

@[simp] theorem get_cons_zero {as : List α} : (a :: as).get ⟨0, Nat.zero_lt_succ _⟩ = a := rfl

@[simp] theorem get_cons_succ {as : List α} {h : i + 1 < (a :: as).length} :
  (a :: as).get ⟨i+1, h⟩ = as.get ⟨i, Nat.lt_of_succ_lt_succ h⟩ := rfl

@[simp] theorem getLast_singleton : [x].getLast (by simp) = x := rfl

@[simp] theorem getLast_cons_cons : (x::y::ys).getLast (by simp) = (y::ys).getLast (by simp) := rfl

theorem get_of_mem : ∀ {a} {l : List α}, a ∈ l → ∃ n, get l n = a
  | _, _ :: _, .head .. => ⟨⟨0, Nat.succ_pos _⟩, rfl⟩
  | _, _ :: _, .tail _ m => let ⟨⟨n, h⟩, e⟩ := get_of_mem m; ⟨⟨n+1, Nat.succ_lt_succ h⟩, e⟩

theorem get?_eq_get : ∀ {l : List α} {n} h, l.get? n = some (get l ⟨n, h⟩)
  | _ :: _, 0, _ => rfl
  | _ :: l, _+1, _ => get?_eq_get (l := l) _

theorem get?_len_le : ∀ {l : List α} {n}, length l ≤ n → l.get? n = none
  | [], _, _ => rfl
  | _ :: l, _+1, h => get?_len_le (l := l) <| Nat.le_of_succ_le_succ h

theorem get?_eq_some : l.get? n = some a ↔ ∃ h, get l ⟨n, h⟩ = a :=
  ⟨fun e =>
    have : n < length l := Nat.lt_of_not_le fun hn => by cases get?_len_le hn ▸ e
    ⟨this, by rwa [get?_eq_get this, Option.some.injEq] at e⟩,
  fun ⟨h, e⟩ => e ▸ get?_eq_get _⟩

@[simp] theorem get?_eq_none : l.get? n = none ↔ length l ≤ n :=
  ⟨fun e => Nat.le_of_not_lt (fun h' => by cases e ▸ get?_eq_some.2 ⟨h', rfl⟩), get?_len_le⟩

theorem get?_of_mem {a} {l : List α} (h : a ∈ l) : ∃ n, l.get? n = some a :=
  let ⟨⟨n, _⟩, e⟩ := get_of_mem h; ⟨n, e ▸ get?_eq_get _⟩

theorem get_mem : ∀ (l : List α) n h, get l ⟨n, h⟩ ∈ l
  | _ :: _, 0, _ => .head ..
  | _ :: l, _+1, _ => .tail _ (get_mem l ..)

theorem get?_mem {l : List α} {n a} (e : l.get? n = some a) : a ∈ l :=
  let ⟨_, e⟩ := get?_eq_some.1 e; e ▸ get_mem ..

theorem mem_iff_get {a} {l : List α} : a ∈ l ↔ ∃ n, get l n = a :=
  ⟨get_of_mem, fun ⟨_, e⟩ => e ▸ get_mem ..⟩

-- TODO(Mario): move somewhere else
theorem Fin.exists_iff (p : Fin n → Prop) : (∃ i, p i) ↔ ∃ i h, p ⟨i, h⟩ :=
  ⟨fun ⟨i, h⟩ => ⟨i.1, i.2, h⟩, fun ⟨i, hi, h⟩ => ⟨⟨i, hi⟩, h⟩⟩

theorem mem_iff_get? {a} {l : List α} : a ∈ l ↔ ∃ n, l.get? n = some a := by
  simp [get?_eq_some, Fin.exists_iff, mem_iff_get]

theorem get?_zero (l : List α) : l.get? 0 = l.head? := by cases l <;> rfl

/-! ### remove nth -/

theorem length_removeNth : ∀ (l : List α) (i : Nat),
  i < length l → length (removeNth l i) = length l - 1
| [], _, _ => rfl
| x::xs, 0, _ => by simp [removeNth]; rfl
| x::xs, i+1, h => by
  have : i < length xs := Nat.lt_of_succ_lt_succ h
  simp [removeNth, ← Nat.add_one]
  rw [length_removeNth xs i this,
    Nat.sub_add_cancel (Nat.lt_of_le_of_lt (Nat.zero_le _) this)]; rfl

/-! ### tail -/

@[simp] theorem length_tail (l : List α) : length (tail l) = length l - 1 := by cases l <;> rfl

/-! ### take and drop -/

@[simp] theorem length_take : ∀ (i : Nat) (l : List α), length (take i l) = min i (length l)
  | 0, l => by simp [Nat.zero_min]
  | succ n, [] => by simp [Nat.min_zero]
  | succ n, _ :: l => by simp [Nat.min_succ_succ, add_one, length_take]

theorem length_take_le (n) (l : List α) : length (take n l) ≤ n := by simp [Nat.min_le_left]

@[simp] theorem length_drop : ∀ (i : Nat) (l : List α), length (drop i l) = length l - i
  | 0, _ => rfl
  | succ i, [] => Eq.symm (Nat.zero_sub (succ i))
  | succ i, x :: l => calc
    length (drop (succ i) (x :: l)) = length l - i := length_drop i l
    _ = succ (length l) - succ i := (Nat.succ_sub_succ_eq_sub (length l) i).symm

@[simp] theorem take_append_drop : ∀ (n : Nat) (l : List α), take n l ++ drop n l = l
  | 0, _ => rfl
  | _+1, [] => rfl
  | n+1, x :: xs => congrArg (cons x) <| take_append_drop n xs

theorem get_cons_drop : ∀ (l : List α) i, List.get l i :: List.drop (i + 1) l = List.drop i l
  | _::_, ⟨0, _⟩ => rfl
  | _::_, ⟨i+1, _⟩ => get_cons_drop _ ⟨i, _⟩

theorem map_eq_append_split {f : α → β} {l : List α} {s₁ s₂ : List β}
    (h : map f l = s₁ ++ s₂) : ∃ l₁ l₂, l = l₁ ++ l₂ ∧ map f l₁ = s₁ ∧ map f l₂ = s₂ := by
  have := h
  rw [← take_append_drop (length s₁) l] at this ⊢
  rw [map_append] at this
  refine ⟨_, _, rfl, append_inj this ?_⟩
  rw [length_map, length_take, Nat.min_eq_left]
  rw [← length_map l f, h, length_append]
  apply Nat.le_add_right

/-! ### reverse -/

@[simp] theorem mem_reverseAux (x : α) : ∀ as bs, x ∈ reverseAux as bs ↔ x ∈ as ∨ x ∈ bs
  | [], _ => by simp
  | a :: _, _ => by simp [mem_reverseAux]; rw [← or_assoc, @or_comm (x = a)]

@[simp] theorem mem_reverse (x : α) (as : List α) : x ∈ reverse as ↔ x ∈ as := by simp [reverse]

/-! ### filter and partition -/

theorem mem_filter : x ∈ filter p as ↔ x ∈ as ∧ p x := by
  induction as with
  | nil => simp [filter]
  | cons a as ih =>
    unfold filter; split <;> simp only [*, mem_cons, or_and_right]
    · exact or_congr_left (and_iff_left_of_imp fun | rfl => ‹_›).symm
    · exact (or_iff_right fun ⟨rfl, h⟩ => (Bool.not_eq_true _).mpr ‹_› h).symm

@[simp] theorem partition_eq_filter_filter (p : α → Bool) (l : List α) :
    partition p l = (filter p l, filter (not ∘ p) l) := by simp [partition, aux] where
  aux : ∀ l {as bs}, partitionAux p l (as, bs) =
    (as.reverse ++ filter p l, bs.reverse ++ filter (not ∘ p) l)
  | [] => by simp [partitionAux, filter]
  | a :: l => by cases pa : p a <;> simp [partitionAux, pa, aux, filter, append_assoc]

/-! ### sublist -/

theorem Sublist.length_le : ∀ {l₁ l₂ : List α}, l₁ <+ l₂ → length l₁ ≤ length l₂
  | _, _, .slnil => Nat.le_refl 0
  | _, _, .cons _ s => le_succ_of_le (length_le s)
  | _, _, .cons2 _ s => succ_le_succ (length_le s)
