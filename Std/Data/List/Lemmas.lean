/-
Copyright (c) 2014 Parikshit Khanna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Parikshit Khanna, Jeremy Avigad, Leonardo de Moura, Floris van Doorn, Mario Carneiro
-/
import Std.Control.ForInStep.Lemmas
import Std.Data.Nat.Lemmas
import Std.Data.List.Basic
import Std.Data.Option.Lemmas
import Std.Classes.BEq
import Std.Tactic.Ext
import Std.Tactic.Simpa

namespace List

open Nat

/-! # Basic properties of Lists -/

theorem cons_ne_nil (a : α) (l : List α) : a :: l ≠ [] := fun.

theorem cons_ne_self (a : α) (l : List α) : a :: l ≠ l := mt (congrArg length) (Nat.succ_ne_self _)

theorem head_eq_of_cons_eq (H : h₁ :: t₁ = h₂ :: t₂) : h₁ = h₂ := (cons.inj H).1

theorem tail_eq_of_cons_eq (H : h₁ :: t₁ = h₂ :: t₂) : t₁ = t₂ := (cons.inj H).2

theorem cons_inj (a : α) {l l' : List α} : a :: l = a :: l' ↔ l = l' :=
  ⟨tail_eq_of_cons_eq, congrArg _⟩

theorem exists_cons_of_ne_nil : ∀ {l : List α}, l ≠ [] → ∃ b L, l = b :: L
  | c :: l', _ => ⟨c, l', rfl⟩

/-! ### length -/

@[simp 1100] theorem length_singleton (a : α) : length [a] = 1 := rfl

theorem length_pos_of_mem {a : α} : ∀ {l : List α}, a ∈ l → 0 < length l
  | _::_, _ => Nat.zero_lt_succ _

theorem exists_mem_of_length_pos : ∀ {l : List α}, 0 < length l → ∃ a, a ∈ l
  | _::_, _ => ⟨_, .head ..⟩

theorem length_pos_iff_exists_mem {l : List α} : 0 < length l ↔ ∃ a, a ∈ l :=
  ⟨exists_mem_of_length_pos, fun ⟨_, h⟩ => length_pos_of_mem h⟩

theorem length_pos {l : List α} : 0 < length l ↔ l ≠ [] :=
  Nat.pos_iff_ne_zero.trans (not_congr length_eq_zero)

theorem exists_mem_of_ne_nil (l : List α) (h : l ≠ []) : ∃ x, x ∈ l :=
  exists_mem_of_length_pos (length_pos.2 h)

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

theorem eq_of_mem_singleton : a ∈ [b] → a = b
  | .head .. => rfl

@[simp 1100] theorem mem_singleton {a b : α} : a ∈ [b] ↔ a = b :=
  ⟨eq_of_mem_singleton, (by simp [·])⟩

theorem mem_of_mem_cons_of_mem : ∀ {a b : α} {l : List α}, a ∈ b :: l → b ∈ l → a ∈ l
  | _, _, _, .head .., h | _, _, _, .tail _ h, _ => h

theorem eq_or_ne_mem_of_mem {a b : α} {l : List α} (h' : a ∈ b :: l) : a = b ∨ (a ≠ b ∧ a ∈ l) :=
  (Classical.em _).imp_right fun h => ⟨h, (mem_cons.1 h').resolve_left h⟩

theorem ne_nil_of_mem {a : α} {l : List α} (h : a ∈ l) : l ≠ [] := by cases h <;> intro.

theorem append_of_mem {a : α} {l : List α} : a ∈ l → ∃ s t : List α, l = s ++ a :: t
  | .head l => ⟨[], l, rfl⟩
  | .tail b h => let ⟨s, t, h'⟩ := append_of_mem h; ⟨b::s, t, by rw [h', cons_append]⟩

@[simp] theorem elem_iff [DecidableEq α] {a : α} {as : List α} :
    elem a as ↔ a ∈ as := ⟨mem_of_elem_eq_true, elem_eq_true_of_mem⟩

theorem mem_of_ne_of_mem {a y : α} {l : List α} (h₁ : a ≠ y) (h₂ : a ∈ y :: l) : a ∈ l :=
  Or.elim (mem_cons.mp h₂) (absurd · h₁) (·)

theorem ne_of_not_mem_cons {a b : α} {l : List α} : a ∉ b::l → a ≠ b := mt (· ▸ .head _)

theorem not_mem_of_not_mem_cons {a b : α} {l : List α} : a ∉ b::l → a ∉ l := mt (.tail _)

theorem not_mem_cons_of_ne_of_not_mem {a y : α} {l : List α} : a ≠ y → a ∉ l → a ∉ y::l :=
  mt ∘ mem_of_ne_of_mem

theorem ne_and_not_mem_of_not_mem_cons {a y : α} {l : List α} : a ∉ y::l → a ≠ y ∧ a ∉ l :=
  fun p => ⟨ne_of_not_mem_cons p, not_mem_of_not_mem_cons p⟩

/-! ### append -/

theorem append_eq_append : List.append l₁ l₂ = l₁ ++ l₂ := rfl

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

@[simp] theorem mem_append {a : α} {s t : List α} : a ∈ s ++ t ↔ a ∈ s ∨ a ∈ t := by
  induction s <;> simp_all [or_assoc]

theorem not_mem_append {a : α} {s t : List α} (h₁ : a ∉ s) (h₂ : a ∉ t) : a ∉ s ++ t :=
  mt mem_append.1 $ not_or.mpr ⟨h₁, h₂⟩

theorem mem_append_eq (a : α) (s t : List α) : (a ∈ s ++ t) = (a ∈ s ∨ a ∈ t) :=
  propext mem_append

theorem mem_append_left {a : α} {l₁ : List α} (l₂ : List α) (h : a ∈ l₁) : a ∈ l₁ ++ l₂ :=
  mem_append.2 (Or.inl h)

theorem mem_append_right {a : α} (l₁ : List α) {l₂ : List α} (h : a ∈ l₂) : a ∈ l₁ ++ l₂ :=
  mem_append.2 (Or.inr h)

theorem mem_iff_append {a : α} {l : List α} : a ∈ l ↔ ∃ s t : List α, l = s ++ a :: t :=
  ⟨append_of_mem, fun ⟨s, t, e⟩ => e ▸ by simp⟩

/-! ### map -/

theorem map_singleton (f : α → β) (a : α) : map f [a] = [f a] := rfl

@[simp] theorem mem_map {f : α → β} : ∀ {l : List α}, b ∈ l.map f ↔ ∃ a, a ∈ l ∧ f a = b
  | [] => by simp
  | _ :: l => by simp [mem_map (l := l), eq_comm (a := b)]

theorem mem_map_of_mem (f : α → β) (h : a ∈ l) : f a ∈ map f l := mem_map.2 ⟨_, h, rfl⟩

theorem exists_of_mem_map (h : b ∈ map f l) : ∃ a, a ∈ l ∧ f a = b := mem_map.1 h

theorem forall_mem_map_iff {f : α → β} {l : List α} {P : β → Prop} :
    (∀ i ∈ l.map f, P i) ↔ ∀ j ∈ l, P (f j) := by
  simp

@[simp] theorem map_eq_nil {f : α → β} {l : List α} : map f l = [] ↔ l = [] := by
  constructor <;> exact fun _ => match l with | [] => rfl

/-! ### zipWith -/

@[simp] theorem length_zipWith (f : α → β → γ) (l₁ l₂) :
    length (zipWith f l₁ l₂) = min (length l₁) (length l₂) := by
  induction l₁ generalizing l₂ <;> cases l₂ <;>
    simp_all [add_one, min_succ_succ, Nat.zero_min, Nat.min_zero]

@[simp]
theorem zipWith_map {μ} (f : γ → δ → μ) (g : α → γ) (h : β → δ) (l₁ : List α) (l₂ : List β) :
    zipWith f (l₁.map g) (l₂.map h) = zipWith (fun a b => f (g a) (h b)) l₁ l₂ := by
  induction l₁ generalizing l₂ <;> cases l₂ <;> simp_all

theorem zipWith_map_left (l₁ : List α) (l₂ : List β) (f : α → α') (g : α' → β → γ) :
    zipWith g (l₁.map f) l₂ = zipWith (fun a b => g (f a) b) l₁ l₂ := by
  induction l₁ generalizing l₂ <;> cases l₂ <;> simp_all

theorem zipWith_map_right (l₁ : List α) (l₂ : List β) (f : β → β') (g : α → β' → γ) :
    zipWith g l₁ (l₂.map f) = zipWith (fun a b => g a (f b)) l₁ l₂ := by
  induction l₁ generalizing l₂ <;> cases l₂ <;> simp_all

theorem zipWith_foldr_eq_zip_foldr {f : α → β → γ} (i : δ):
    (zipWith f l₁ l₂).foldr g i = (zip l₁ l₂).foldr (fun p r => g (f p.1 p.2) r) i := by
  induction l₁ generalizing l₂ <;> cases l₂ <;> simp_all

theorem zipWith_foldl_eq_zip_foldl {f : α → β → γ} (i : δ):
    (zipWith f l₁ l₂).foldl g i = (zip l₁ l₂).foldl (fun r p => g r (f p.1 p.2)) i := by
  induction l₁ generalizing i l₂ <;> cases l₂ <;> simp_all

/-! ### zip -/

@[simp] theorem length_zip (l₁ : List α) (l₂ : List β) :
    length (zip l₁ l₂) = min (length l₁) (length l₂) := by
  simp [zip]

theorem zip_map (f : α → γ) (g : β → δ) :
    ∀ (l₁ : List α) (l₂ : List β), zip (l₁.map f) (l₂.map g) = (zip l₁ l₂).map (Prod.map f g)
  | [], l₂ => rfl
  | l₁, [] => by simp only [map, zip_nil_right]
  | a :: l₁, b :: l₂ => by
    simp only [map, zip_cons_cons, zip_map, Prod.map]; constructor

theorem zip_map_left (f : α → γ) (l₁ : List α) (l₂ : List β) :
    zip (l₁.map f) l₂ = (zip l₁ l₂).map (Prod.map f id) := by rw [← zip_map, map_id]

theorem zip_map_right (f : β → γ) (l₁ : List α) (l₂ : List β) :
    zip l₁ (l₂.map f) = (zip l₁ l₂).map (Prod.map id f) := by rw [← zip_map, map_id]

/-! ### join -/

theorem mem_join : ∀ {L : List (List α)}, a ∈ L.join ↔ ∃ l, l ∈ L ∧ a ∈ l
  | [] => by simp
  | b :: l => by simp [mem_join, or_and_right, exists_or]

theorem exists_of_mem_join : a ∈ join L → ∃ l, l ∈ L ∧ a ∈ l := mem_join.1

theorem mem_join_of_mem (lL : l ∈ L) (al : a ∈ l) : a ∈ join L := mem_join.2 ⟨l, lL, al⟩

/-! ### bind -/

theorem mem_bind {f : α → List β} {b} {l : List α} : b ∈ l.bind f ↔ ∃ a, a ∈ l ∧ b ∈ f a := by
  simp [List.bind, mem_join]
  exact ⟨fun ⟨_, ⟨a, h₁, rfl⟩, h₂⟩ => ⟨a, h₁, h₂⟩, fun ⟨a, h₁, h₂⟩ => ⟨_, ⟨a, h₁, rfl⟩, h₂⟩⟩

theorem exists_of_mem_bind {b : β} {l : List α} {f : α → List β} :
    b ∈ List.bind l f → ∃ a, a ∈ l ∧ b ∈ f a := mem_bind.1

theorem mem_bind_of_mem {b : β} {l : List α} {f : α → List β} {a} (al : a ∈ l) (h : b ∈ f a) :
    b ∈ List.bind l f := mem_bind.2 ⟨a, al, h⟩

theorem bind_map (f : β → γ) (g : α → List β) :
    ∀ l : List α, map f (l.bind g) = l.bind fun a => (g a).map f
  | [] => rfl
  | a::l => by simp only [cons_bind, map_append, bind_map _ _ l]

/-! ### set-theoretic notation of Lists -/

@[simp] theorem empty_eq : (∅ : List α) = [] := rfl

/-! ### bounded quantifiers over Lists -/

theorem exists_mem_nil (p : α → Prop) : ¬∃ x ∈ @nil α, p x := fun.

theorem forall_mem_nil (p : α → Prop) : ∀ x ∈ @nil α, p x := fun.

theorem exists_mem_cons {p : α → Prop} {a : α} {l : List α} :
    (∃ x ∈ a :: l, p x) ↔ p a ∨ ∃ x ∈ l, p x := by simp

theorem forall_mem_singleton {p : α → Prop} {a : α} : (∀ x ∈ [a], p x) ↔ p a := by
  simp only [mem_singleton, forall_eq]

theorem forall_mem_append {p : α → Prop} {l₁ l₂ : List α} :
    (∀ x ∈ l₁ ++ l₂, p x) ↔ (∀ x ∈ l₁, p x) ∧ (∀ x ∈ l₂, p x) := by
  simp only [mem_append, or_imp, forall_and]

/-! ### List subset -/

theorem subset_def {l₁ l₂ : List α} : l₁ ⊆ l₂ ↔ ∀ {a : α}, a ∈ l₁ → a ∈ l₂ := .rfl

@[simp] theorem nil_subset (l : List α) : [] ⊆ l := fun.

@[simp] theorem Subset.refl (l : List α) : l ⊆ l := fun _ i => i

theorem Subset.trans {l₁ l₂ l₃ : List α} (h₁ : l₁ ⊆ l₂) (h₂ : l₂ ⊆ l₃) : l₁ ⊆ l₃ :=
  fun _ i => h₂ (h₁ i)

instance : Trans (Membership.mem : α → List α → Prop) Subset Membership.mem :=
  ⟨fun h₁ h₂ => h₂ h₁⟩

instance : Trans (Subset : List α → List α → Prop) Subset Subset :=
  ⟨Subset.trans⟩

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
  simp only [subset_def, mem_cons, or_imp, forall_and, forall_eq]

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

theorem eq_replicate_of_mem {a : α} :
    ∀ {l : List α}, (∀ b ∈ l, b = a) → l = replicate l.length a
  | [], _ => rfl
  | b :: l, H => by
    let ⟨rfl, H₂⟩ := forall_mem_cons.1 H
    rw [length_cons, replicate, ← eq_replicate_of_mem H₂]

theorem eq_replicate {a : α} {n} {l : List α} :
    l = replicate n a ↔ length l = n ∧ ∀ b ∈ l, b = a :=
  ⟨fun h => h ▸ ⟨length_replicate .., fun _ => eq_of_mem_replicate⟩,
   fun ⟨e, al⟩ => e ▸ eq_replicate_of_mem al⟩

/-! ### getLast -/

theorem getLast_cons' {a : α} {l : List α} : ∀ (h₁ : a :: l ≠ nil) (h₂ : l ≠ nil),
  getLast (a :: l) h₁ = getLast l h₂ := by
  induction l <;> intros; {contradiction}; rfl

@[simp] theorem getLast_append {a : α} : ∀ (l : List α) h, getLast (l ++ [a]) h = a
  | [], _ => rfl
  | a::t, h => by
    simp [getLast_cons' _ fun H => cons_ne_nil _ _ (append_eq_nil.1 H).2, getLast_append t]

theorem getLast_concat : (h : concat l a ≠ []) → getLast (concat l a) h = a :=
  concat_eq_append .. ▸ getLast_append _

theorem eq_nil_or_concat : ∀ l : List α, l = [] ∨ ∃ L b, l = L ++ [b]
  | [] => .inl rfl
  | a::l => match l, eq_nil_or_concat l with
    | _, .inl rfl => .inr ⟨[], a, rfl⟩
    | _, .inr ⟨L, b, rfl⟩ => .inr ⟨a::L, b, rfl⟩

/-! ### sublists -/

@[simp] theorem nil_sublist : ∀ l : List α, [] <+ l
  | [] => .slnil
  | a :: l => (nil_sublist l).cons a

@[simp] theorem Sublist.refl : ∀ l : List α, l <+ l
  | [] => .slnil
  | a :: l => (Sublist.refl l).cons₂ a

theorem Sublist.trans {l₁ l₂ l₃ : List α} (h₁ : l₁ <+ l₂) (h₂ : l₂ <+ l₃) : l₁ <+ l₃ := by
  induction h₂ generalizing l₁ with
  | slnil => exact h₁
  | cons _ _ IH => exact (IH h₁).cons _
  | @cons₂ l₂ _ a _ IH =>
    generalize e : a :: l₂ = l₂'
    match e ▸ h₁ with
    | .slnil => apply nil_sublist
    | .cons a' h₁' => cases e; apply (IH h₁').cons
    | .cons₂ a' h₁' => cases e; apply (IH h₁').cons₂

instance : Trans (@Sublist α) Sublist Sublist := ⟨Sublist.trans⟩

@[simp] theorem sublist_cons (a : α) (l : List α) : l <+ a :: l := (Sublist.refl l).cons _

theorem sublist_of_cons_sublist : a :: l₁ <+ l₂ → l₁ <+ l₂ :=
  (sublist_cons a l₁).trans

@[simp] theorem sublist_append_left : ∀ l₁ l₂ : List α, l₁ <+ l₁ ++ l₂
  | [], _ => nil_sublist _
  | _ :: l₁, l₂ => (sublist_append_left l₁ l₂).cons₂ _

@[simp] theorem sublist_append_right : ∀ l₁ l₂ : List α, l₂ <+ l₁ ++ l₂
  | [], _ => Sublist.refl _
  | _ :: l₁, l₂ => (sublist_append_right l₁ l₂).cons _

theorem sublist_append_of_sublist_left (s : l <+ l₁) : l <+ l₁ ++ l₂ :=
  s.trans <| sublist_append_left ..

theorem sublist_append_of_sublist_right (s : l <+ l₂) : l <+ l₁ ++ l₂ :=
  s.trans <| sublist_append_right ..

theorem cons_sublist_cons : a :: l₁ <+ a :: l₂ ↔ l₁ <+ l₂ :=
  ⟨fun | .cons _ s => sublist_of_cons_sublist s | .cons₂ _ s => s, .cons₂ _⟩

@[simp] theorem append_sublist_append_left : ∀ l, l ++ l₁ <+ l ++ l₂ ↔ l₁ <+ l₂
  | [] => Iff.rfl
  | _ :: l => cons_sublist_cons.trans (append_sublist_append_left l)

theorem Sublist.append_left : l₁ <+ l₂ → ∀ l, l ++ l₁ <+ l ++ l₂ :=
  fun h l => (append_sublist_append_left l).mpr h

theorem Sublist.append_right : l₁ <+ l₂ → ∀ l, l₁ ++ l <+ l₂ ++ l
  | .slnil, _ => Sublist.refl _
  | .cons _ h, _ => (h.append_right _).cons _
  | .cons₂ _ h, _ => (h.append_right _).cons₂ _

theorem sublist_or_mem_of_sublist (h : l <+ l₁ ++ a :: l₂) : l <+ l₁ ++ l₂ ∨ a ∈ l := by
  induction l₁ generalizing l with
  | nil => match h with
    | .cons _ h => exact .inl h
    | .cons₂ _ h => exact .inr (.head ..)
  | cons b l₁ IH =>
    match h with
    | .cons _ h => exact (IH h).imp_left (Sublist.cons _)
    | .cons₂ _ h => exact (IH h).imp (Sublist.cons₂ _) (.tail _)

theorem Sublist.reverse : l₁ <+ l₂ → l₁.reverse <+ l₂.reverse
  | .slnil => Sublist.refl _
  | .cons _ h => by rw [reverse_cons]; exact sublist_append_of_sublist_left h.reverse
  | .cons₂ _ h => by rw [reverse_cons, reverse_cons]; exact h.reverse.append_right _

@[simp] theorem reverse_sublist : l₁.reverse <+ l₂.reverse ↔ l₁ <+ l₂ :=
  ⟨fun h => l₁.reverse_reverse ▸ l₂.reverse_reverse ▸ h.reverse, Sublist.reverse⟩

@[simp] theorem append_sublist_append_right (l) : l₁ ++ l <+ l₂ ++ l ↔ l₁ <+ l₂ :=
  ⟨fun h => by
    have := h.reverse
    simp only [reverse_append, append_sublist_append_left, reverse_sublist] at this
    exact this,
   fun h => h.append_right l⟩

theorem Sublist.append (hl : l₁ <+ l₂) (hr : r₁ <+ r₂) : l₁ ++ r₁ <+ l₂ ++ r₂ :=
  (hl.append_right _).trans ((append_sublist_append_left _).2 hr)

theorem Sublist.subset : l₁ <+ l₂ → l₁ ⊆ l₂
  | .slnil, _, h => h
  | .cons _ s, _, h => .tail _ (s.subset h)
  | .cons₂ .., _, .head .. => .head ..
  | .cons₂ _ s, _, .tail _ h => .tail _ (s.subset h)

instance : Trans (@Sublist α) Subset Subset :=
  ⟨fun h₁ h₂ => trans h₁.subset h₂⟩

instance : Trans Subset (@Sublist α) Subset :=
  ⟨fun h₁ h₂ => trans h₁ h₂.subset⟩

instance : Trans (Membership.mem : α → List α → Prop) Sublist Membership.mem :=
  ⟨fun h₁ h₂ => h₂.subset h₁⟩

theorem Sublist.length_le : l₁ <+ l₂ → length l₁ ≤ length l₂
  | .slnil => Nat.le_refl 0
  | .cons _l s => le_succ_of_le (length_le s)
  | .cons₂ _ s => succ_le_succ (length_le s)

@[simp] theorem sublist_nil {l : List α} : l <+ [] ↔ l = [] :=
  ⟨fun s => subset_nil.1 s.subset, fun H => H ▸ Sublist.refl _⟩

theorem Sublist.eq_of_length : l₁ <+ l₂ → length l₁ = length l₂ → l₁ = l₂
  | .slnil, _ => rfl
  | .cons a s, h => nomatch Nat.not_lt.2 s.length_le (h ▸ lt_succ_self _)
  | .cons₂ a s, h => by rw [s.eq_of_length (succ.inj h)]

theorem Sublist.eq_of_length_le (s : l₁ <+ l₂) (h : length l₂ ≤ length l₁) : l₁ = l₂ :=
  s.eq_of_length <| Nat.le_antisymm s.length_le h

@[simp] theorem singleton_sublist {a : α} {l} : [a] <+ l ↔ a ∈ l := by
  refine ⟨fun h => h.subset (mem_singleton_self _), fun h => ?_⟩
  obtain ⟨_, _, rfl⟩ := append_of_mem h
  exact ((nil_sublist _).cons₂ _).trans (sublist_append_right ..)

@[simp] theorem replicate_sublist_replicate {m n} (a : α) :
    replicate m a <+ replicate n a ↔ m ≤ n := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · have := h.length_le; simp only [length_replicate] at this ⊢; exact this
  · induction h with
    | refl => apply Sublist.refl
    | step => simp [*, replicate, Sublist.cons]

theorem isSublist_iff_sublist [DecidableEq α] {l₁ l₂ : List α} : l₁.isSublist l₂ ↔ l₁ <+ l₂ := by
  cases l₁ <;> cases l₂ <;> simp [isSublist]
  case cons.cons hd₁ tl₁ hd₂ tl₂ =>
    if h_eq : hd₁ = hd₂ then
      simp [h_eq, cons_sublist_cons, isSublist_iff_sublist]
    else
      simp only [h_eq]
      constructor
      · intro h_sub
        apply Sublist.cons
        exact isSublist_iff_sublist.mp h_sub
      · intro h_sub
        cases h_sub
        case cons h_sub =>
          exact isSublist_iff_sublist.mpr h_sub
        case cons₂ =>
          contradiction

instance [DecidableEq α] (l₁ l₂ : List α) : Decidable (l₁ <+ l₂) :=
  decidable_of_iff (l₁.isSublist l₂) isSublist_iff_sublist

/-! ### head -/

theorem head!_of_head? [Inhabited α] : ∀ {l : List α}, head? l = some a → head! l = a
  | _a::_l, rfl => rfl

theorem head?_eq_head : ∀ l h, @head? α l = some (head l h)
  | [], h => nomatch h rfl
  | _::_, _ => rfl

/-! ### tail -/

@[simp] theorem tailD_eq_tail? (l l' : List α) : tailD l l' = (tail? l).getD l' := by
  cases l <;> rfl

theorem tail_eq_tailD (l) : @tail α l = tailD l [] := by cases l <;> rfl

theorem tail_eq_tail? (l) : @tail α l = (tail? l).getD [] := by simp [tail_eq_tailD]

/-! ### next? -/

@[simp] theorem next?_nil : @next? α [] = none := rfl
@[simp] theorem next?_cons (a l) : @next? α (a :: l) = some (a, l) := rfl

/-! ### getLast -/

@[simp] theorem getLastD_nil (a) : @getLastD α [] a = a := rfl
@[simp] theorem getLastD_cons (a b l) : @getLastD α (b::l) a = getLastD l b := by cases l <;> rfl

theorem getLast_eq_getLastD (a l h) : @getLast α (a::l) h = getLastD l a := by
  cases l <;> rfl

theorem getLastD_eq_getLast? (a l) : @getLastD α l a = (getLast? l).getD a := by
  cases l <;> rfl

theorem getLast_singleton (a h) : @getLast α [a] h = a := rfl

theorem getLast!_cons [Inhabited α] : @getLast! α _ (a::l) = getLastD l a := by
  simp [getLast!, getLast_eq_getLastD]

@[simp] theorem getLast?_nil : @getLast? α [] = none := rfl
theorem getLast?_cons : @getLast? α (a::l) = getLastD l a := by
  simp [getLast?, getLast_eq_getLastD]

theorem getLast?_eq_getLast : ∀ l h, @getLast? α l = some (getLast l h)
  | [], h => nomatch h rfl
  | _::_, _ => rfl

/-! ### dropLast -/

@[simp] theorem dropLast_append_cons : dropLast (l₁ ++ b::l₂) = l₁ ++ dropLast (b::l₂) := by
  induction l₁ <;> simp [*, dropLast]

@[simp 1100] theorem dropLast_concat : dropLast (l₁ ++ [b]) = l₁ := by simp

/-! ### nth element -/

@[simp] theorem get_cons_succ {as : List α} {h : i + 1 < (a :: as).length} :
  (a :: as).get ⟨i+1, h⟩ = as.get ⟨i, Nat.lt_of_succ_lt_succ h⟩ := rfl

@[simp] theorem get_cons_succ' {as : List α} {i : Fin as.length} :
  (a :: as).get i.succ = as.get i := rfl

@[simp] theorem get_cons_cons_one : (a₁ :: a₂ :: as).get (1 : Fin (as.length + 2)) = a₂ := rfl

theorem get_of_mem : ∀ {a} {l : List α}, a ∈ l → ∃ n, get l n = a
  | _, _ :: _, .head .. => ⟨⟨0, Nat.succ_pos _⟩, rfl⟩
  | _, _ :: _, .tail _ m => let ⟨⟨n, h⟩, e⟩ := get_of_mem m; ⟨⟨n+1, Nat.succ_lt_succ h⟩, e⟩

theorem get?_eq_get : ∀ {l : List α} {n} (h : n < l.length), l.get? n = some (get l ⟨n, h⟩)
  | _ :: _, 0, _ => rfl
  | _ :: l, _+1, _ => get?_eq_get (l := l) _

theorem get!_cons_succ [Inhabited α] (l : List α) (a : α) (n : Nat) :
    (a::l).get! (n+1) = get! l n := rfl

theorem get!_cons_zero [Inhabited α] (l : List α) (a : α) : (a::l).get! 0 = a := rfl

theorem get!_nil [Inhabited α] (n : Nat) : [].get! n = (default : α) := rfl

theorem get?_len_le : ∀ {l : List α} {n}, length l ≤ n → l.get? n = none
  | [], _, _ => rfl
  | _ :: l, _+1, h => get?_len_le (l := l) <| Nat.le_of_succ_le_succ h

theorem get!_len_le [Inhabited α] : ∀ {l : List α} {n}, length l ≤ n → l.get! n = (default : α)
  | [], _, _ => rfl
  | _ :: l, _+1, h => get!_len_le (l := l) <| Nat.le_of_succ_le_succ h

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

@[simp] theorem getElem_eq_get (l : List α) (i : Nat) (h) : l[i]'h = l.get ⟨i, h⟩ := rfl

@[simp] theorem getElem?_eq_get? (l : List α) (i : Nat) : l[i]? = l.get? i := by
  unfold getElem?; split
  · exact (get?_eq_get ‹_›).symm
  · exact (get?_eq_none.2 <| Nat.not_lt.1 ‹_›).symm

theorem get?_inj
    (h₀ : i < xs.length) (h₁ : Nodup xs) (h₂ : xs.get? i = xs.get? j) : i = j := by
  induction xs generalizing i j with
  | nil => cases h₀
  | cons x xs ih =>
    match i, j with
    | 0, 0 => rfl
    | i+1, j+1 => simp; cases h₁ with
      | cons ha h₁ => exact ih (Nat.lt_of_succ_lt_succ h₀) h₁ h₂
    | i+1, 0 => ?_ | 0, j+1 => ?_
    all_goals
      simp at h₂
      cases h₁; rename_i h' h
      have := h x ?_ rfl; cases this
      rw [mem_iff_get?]
    exact ⟨_, h₂⟩; exact ⟨_ , h₂.symm⟩

@[simp] theorem get?_map (f : α → β) : ∀ l n, (map f l).get? n = (l.get? n).map f
  | [], _ => rfl
  | _ :: _, 0 => rfl
  | _ :: l, n+1 => get?_map f l n

@[simp] theorem get_map (f : α → β) {l n} : get (map f l) n = f (get l ⟨n, length_map l f ▸ n.2⟩) :=
  Option.some.inj <| by rw [← get?_eq_get, get?_map, get?_eq_get]; rfl

/--
If one has `get l i hi` in a formula and `h : l = l'`, one can not `rw h` in the formula as
`hi` gives `i < l.length` and not `i < l'.length`. The theorem `get_of_eq` can be used to make
such a rewrite, with `rw (get_of_eq h)`.
-/
theorem get_of_eq {l l' : List α} (h : l = l') (i : Fin l.length) :
    get l i = get l' ⟨i, h ▸ i.2⟩ := by cases h; rfl

@[simp] theorem get_singleton (a : α) : (n : Fin 1) → get [a] n = a
  | ⟨0, _⟩ => rfl

theorem get_zero : ∀ {l : List α} (h : 0 < l.length), l.get ⟨0, h⟩ = l.head?
  | _::_, _ => rfl

theorem get_append : ∀ {l₁ l₂ : List α} (n : Nat) (h : n < l₁.length),
    (l₁ ++ l₂).get ⟨n, length_append .. ▸ Nat.lt_add_right _ _ _ h⟩ = l₁.get ⟨n, h⟩
| a :: l, _, 0, h => rfl
| a :: l, _, n+1, h => by simp only [get, cons_append]; apply get_append

theorem get?_append_right : ∀ {l₁ l₂ : List α} {n : Nat}, l₁.length ≤ n →
  (l₁ ++ l₂).get? n = l₂.get? (n - l₁.length)
| [], _, n, _ => rfl
| a :: l, _, n+1, h₁ => by rw [cons_append]; simp [get?_append_right (Nat.lt_succ.1 h₁)]

theorem get_append_right_aux {l₁ l₂ : List α} {n : Nat}
  (h₁ : l₁.length ≤ n) (h₂ : n < (l₁ ++ l₂).length) : n - l₁.length < l₂.length := by
  rw [length_append] at h₂
  exact Nat.sub_lt_left_of_lt_add h₁ h₂

theorem get_append_right' {l₁ l₂ : List α} {n : Nat} (h₁ : l₁.length ≤ n) (h₂) :
    (l₁ ++ l₂).get ⟨n, h₂⟩ = l₂.get ⟨n - l₁.length, get_append_right_aux h₁ h₂⟩ :=
Option.some.inj <| by rw [← get?_eq_get, ← get?_eq_get, get?_append_right h₁]

theorem get_of_append_proof {l : List α}
    (eq : l = l₁ ++ a :: l₂) (h : l₁.length = n) : n < length l := eq ▸ h ▸ by simp_arith

theorem get_of_append {l : List α} (eq : l = l₁ ++ a :: l₂) (h : l₁.length = n) :
    l.get ⟨n, get_of_append_proof eq h⟩ = a := Option.some.inj <| by
  rw [← get?_eq_get, eq, get?_append_right (h ▸ Nat.le_refl _), h, Nat.sub_self]; rfl

@[simp] theorem get_replicate (a : α) {n : Nat} (m : Fin _) : (replicate n a).get m = a :=
  eq_of_mem_replicate (get_mem _ _ _)

theorem get?_append {l₁ l₂ : List α} {n : Nat} (hn : n < l₁.length) :
  (l₁ ++ l₂).get? n = l₁.get? n := by
  have hn' : n < (l₁ ++ l₂).length := Nat.lt_of_lt_of_le hn <|
    length_append .. ▸ Nat.le_add_right ..
  rw [get?_eq_get hn, get?_eq_get hn', get_append]

theorem getLast_eq_get : ∀ (l : List α) (h : l ≠ []),
    getLast l h = l.get ⟨l.length - 1, Nat.sub_lt (length_pos.2 h) Nat.one_pos⟩
  | [a], h => by
    rw [getLast_singleton, get_singleton]
  | a :: b :: l, h => by rw [getLast_cons', getLast_eq_get (b :: l)]; {rfl}; exact cons_ne_nil b l

theorem getLast?_eq_get? : ∀ (l : List α), getLast? l = l.get? (l.length - 1)
  | [] => rfl
  | a::l => by rw [getLast?_eq_getLast (a::l) fun., getLast_eq_get, get?_eq_get]

@[simp] theorem get?_concat_length : ∀ (l : List α) (a : α), (l ++ [a]).get? l.length = some a
  | [], a => rfl
  | b :: l, a => by rw [cons_append, length_cons]; simp only [get?, get?_concat_length]

@[simp] theorem getLast?_concat (l : List α) : getLast? (l ++ [a]) = some a := by
  simp [getLast?_eq_get?]

@[simp] theorem getLastD_concat (a b l) : @getLastD α (l ++ [b]) a = b := by
  rw [getLastD_eq_getLast?, getLast?_concat]; rfl

theorem get_cons_length (x : α) (xs : List α) (n : Nat) (h : n = xs.length) :
    (x :: xs).get ⟨n, by simp [h]⟩ = (x :: xs).getLast (cons_ne_nil x xs) := by
  rw [getLast_eq_get]; cases h; rfl

@[ext] theorem ext : ∀ {l₁ l₂ : List α}, (∀ n, l₁.get? n = l₂.get? n) → l₁ = l₂
  | [], [], _ => rfl
  | a :: l₁, [], h => nomatch h 0
  | [], a' :: l₂, h => nomatch h 0
  | a :: l₁, a' :: l₂, h => by
    have h0 : some a = some a' := h 0
    injection h0 with aa; simp only [aa, ext fun n => h (n+1)]

theorem ext_get {l₁ l₂ : List α} (hl : length l₁ = length l₂)
    (h : ∀ n h₁ h₂, get l₁ ⟨n, h₁⟩ = get l₂ ⟨n, h₂⟩) : l₁ = l₂ :=
  ext fun n =>
    if h₁ : n < length l₁ then by
      rw [get?_eq_get, get?_eq_get, h n h₁ (by rwa [← hl])]
    else by
      have h₁ := Nat.le_of_not_lt h₁
      rw [get?_len_le h₁, get?_len_le]; rwa [← hl]

theorem get?_reverse' : ∀ {l : List α} (i j), i + j + 1 = length l →
    get? l.reverse i = get? l j
  | [], _, _, _ => rfl
  | a::l, i, 0, h => by simp at h; simp [h, get?_append_right]
  | a::l, i, j+1, h => by
    have := Nat.succ.inj h; simp at this ⊢
    rw [get?_append, get?_reverse' _ j this]
    rw [length_reverse, ← this]; apply Nat.lt_add_of_pos_right (Nat.succ_pos _)

theorem get?_reverse {l : List α} (i) (h : i < length l) :
    get? l.reverse i = get? l (l.length - 1 - i) :=
  get?_reverse' _ _ <| by
    rw [Nat.add_sub_of_le (Nat.le_pred_of_lt h),
      Nat.sub_add_cancel (Nat.lt_of_le_of_lt (Nat.zero_le _) h)]

theorem get!_of_get? [Inhabited α] : ∀ {l : List α} {n}, get? l n = some a → get! l n = a
  | _a::_, 0, rfl => rfl
  | _::l, _+1, e => get!_of_get? (l := l) e

theorem getD_eq_get? : ∀ l n (a : α), getD l n a = (get? l n).getD a
  | [], _, _ => rfl
  | _a::_, 0, _ => rfl
  | _::l, _+1, _ => getD_eq_get? (l := l) ..

@[simp] theorem get!_eq_getD [Inhabited α] : ∀ (l : List α) n, l.get! n = l.getD n default
  | [], _      => rfl
  | _a::_, 0   => rfl
  | _a::l, n+1 => get!_eq_getD l n

/-! ### take and drop -/

@[simp] theorem take_succ_cons : (a :: as).take (i + 1) = a :: as.take i := rfl

@[simp] theorem length_take : ∀ (i : Nat) (l : List α), length (take i l) = min i (length l)
  | 0, l => by simp [Nat.zero_min]
  | succ n, [] => by simp [Nat.min_zero]
  | succ n, _ :: l => by simp [Nat.min_succ_succ, add_one, length_take]

theorem length_take_le (n) (l : List α) : length (take n l) ≤ n := by simp [Nat.min_le_left]

theorem length_take_of_le (h : n ≤ length l) : length (take n l) = n := by simp [Nat.min_eq_left h]

theorem get_cons_drop : ∀ (l : List α) i, get l i :: drop (i + 1) l = drop i l
  | _::_, ⟨0, _⟩ => rfl
  | _::_, ⟨i+1, _⟩ => get_cons_drop _ ⟨i, _⟩

theorem drop_eq_nil_of_eq_nil : ∀ {as : List α} {i}, as = [] → as.drop i = []
  | _, _, rfl => drop_nil

theorem take_eq_nil_of_eq_nil : ∀ {as : List α} {i}, as = [] → as.take i = []
  | _, _, rfl => take_nil

theorem ne_nil_of_drop_ne_nil {as : List α} {i : Nat} (h: as.drop i ≠ []) : as ≠ [] :=
  mt drop_eq_nil_of_eq_nil h

theorem ne_nil_of_take_ne_nil {as : List α} {i : Nat} (h: as.take i ≠ []) : as ≠ [] :=
  mt take_eq_nil_of_eq_nil h

theorem map_eq_append_split {f : α → β} {l : List α} {s₁ s₂ : List β}
    (h : map f l = s₁ ++ s₂) : ∃ l₁ l₂, l = l₁ ++ l₂ ∧ map f l₁ = s₁ ∧ map f l₂ = s₂ := by
  have := h
  rw [← take_append_drop (length s₁) l] at this ⊢
  rw [map_append] at this
  refine ⟨_, _, rfl, append_inj this ?_⟩
  rw [length_map, length_take, Nat.min_eq_left]
  rw [← length_map l f, h, length_append]
  apply Nat.le_add_right

/-- Dropping the elements up to `n` in `l₁ ++ l₂` is the same as dropping the elements up to `n`
in `l₁`, dropping the elements up to `n - l₁.length` in `l₂`, and appending them. -/
theorem drop_append_eq_append_drop {l₁ l₂ : List α} :
    drop n (l₁ ++ l₂) = drop n l₁ ++ drop (n - l₁.length) l₂ := by
  induction l₁ generalizing n; · simp
  cases n <;> simp [*]

theorem drop_append_of_le_length {l₁ l₂ : List α} (h : n ≤ l₁.length) :
    (l₁ ++ l₂).drop n = l₁.drop n ++ l₂ := by
  simp [drop_append_eq_append_drop, Nat.sub_eq_zero_of_le h]

/-! ### modify nth -/

theorem modifyNthTail_id : ∀ n (l : List α), l.modifyNthTail id n = l
  | 0, _ => rfl
  | _+1, [] => rfl
  | n+1, a :: l => congrArg (cons a) (modifyNthTail_id n l)

theorem removeNth_eq_nth_tail : ∀ n (l : List α), removeNth l n = modifyNthTail tail n l
  | 0, l => by cases l <;> rfl
  | n+1, [] => rfl
  | n+1, a :: l => congrArg (cons _) (removeNth_eq_nth_tail _ _)

theorem get?_modifyNth (f : α → α) :
    ∀ n (l : List α) m, (modifyNth f n l).get? m = (fun a => if n = m then f a else a) <$> l.get? m
  | n, l, 0 => by cases l <;> cases n <;> rfl
  | n, [], _+1 => by cases n <;> rfl
  | 0, _ :: l, m+1 => by cases l.get? m <;> rfl
  | n+1, a :: l, m+1 =>
    (get?_modifyNth f n l m).trans <| by
      cases l.get? m <;> by_cases h : n = m <;>
        simp only [h, if_pos, if_true, if_false, Option.map, mt Nat.succ.inj, not_false_iff]

theorem modifyNthTail_length (f : List α → List α) (H : ∀ l, length (f l) = length l) :
    ∀ n l, length (modifyNthTail f n l) = length l
  | 0, _ => H _
  | _+1, [] => rfl
  | _+1, _ :: _ => congrArg (·+1) (modifyNthTail_length _ H _ _)

theorem modifyNthTail_add (f : List α → List α) (n) (l₁ l₂ : List α) :
    modifyNthTail f (l₁.length + n) (l₁ ++ l₂) = l₁ ++ modifyNthTail f n l₂ := by
  induction l₁ <;> simp [*, Nat.succ_add]

theorem exists_of_modifyNthTail (f : List α → List α) {n} {l : List α} (h : n ≤ l.length) :
    ∃ l₁ l₂, l = l₁ ++ l₂ ∧ l₁.length = n ∧ modifyNthTail f n l = l₁ ++ f l₂ :=
  have ⟨_, _, eq, hl⟩ : ∃ l₁ l₂, l = l₁ ++ l₂ ∧ l₁.length = n :=
    ⟨_, _, (take_append_drop n l).symm, length_take_of_le h⟩
  ⟨_, _, eq, hl, hl ▸ eq ▸ modifyNthTail_add (n := 0) ..⟩

@[simp] theorem modify_get?_length (f : α → α) : ∀ n l, length (modifyNth f n l) = length l :=
  modifyNthTail_length _ fun l => by cases l <;> rfl

@[simp] theorem get?_modifyNth_eq (f : α → α) (n) (l : List α) :
  (modifyNth f n l).get? n = f <$> l.get? n := by
  simp only [get?_modifyNth, if_pos]

@[simp] theorem get?_modifyNth_ne (f : α → α) {m n} (l : List α) (h : m ≠ n) :
    (modifyNth f m l).get? n = l.get? n := by
  simp only [get?_modifyNth, if_neg h, id_map']

theorem exists_of_modifyNth (f : α → α) {n} {l : List α} (h : n < l.length) :
    ∃ l₁ a l₂, l = l₁ ++ a :: l₂ ∧ l₁.length = n ∧ modifyNth f n l = l₁ ++ f a :: l₂ :=
  match exists_of_modifyNthTail _ (Nat.le_of_lt h) with
  | ⟨_, _::_, eq, hl, H⟩ => ⟨_, _, _, eq, hl, H⟩
  | ⟨_, [], eq, hl, _⟩ => nomatch Nat.ne_of_gt h (eq ▸ append_nil _ ▸ hl)

/-! ### set -/

theorem set_eq_modifyNth (a : α) : ∀ n (l : List α), set l n a = modifyNth (fun _ => a) n l
  | 0, l => by cases l <;> rfl
  | n+1, [] => rfl
  | n+1, b :: l => congrArg (cons _) (set_eq_modifyNth _ _ _)

theorem modifyNth_eq_set_get? (f : α → α) :
    ∀ n (l : List α), l.modifyNth f n = ((fun a => l.set n (f a)) <$> l.get? n).getD l
  | 0, l => by cases l <;> rfl
  | n+1, [] => rfl
  | n+1, b :: l =>
    (congrArg (cons _) (modifyNth_eq_set_get? ..)).trans <| by cases l.get? n <;> rfl

theorem modifyNth_eq_set_get (f : α → α) {n} {l : List α} (h) :
    l.modifyNth f n = l.set n (f (l.get ⟨n, h⟩)) := by
  rw [modifyNth_eq_set_get?, get?_eq_get h]; rfl

theorem exists_of_set {l : List α} (h : n < l.length) :
    ∃ l₁ a l₂, l = l₁ ++ a :: l₂ ∧ l₁.length = n ∧ l.set n a' = l₁ ++ a' :: l₂ := by
  rw [set_eq_modifyNth]; exact exists_of_modifyNth _ h

theorem exists_of_set' {l : List α} (h : n < l.length) :
    ∃ l₁ l₂, l = l₁ ++ l.get ⟨n, h⟩ :: l₂ ∧ l₁.length = n ∧ l.set n a' = l₁ ++ a' :: l₂ :=
  have ⟨_, _, _, h₁, h₂, h₃⟩ := exists_of_set h; ⟨_, _, get_of_append h₁ h₂ ▸ h₁, h₂, h₃⟩

theorem get?_set_eq (a : α) (n) (l : List α) : (set l n a).get? n = (fun _ => a) <$> l.get? n := by
  simp only [set_eq_modifyNth, get?_modifyNth_eq]

theorem get?_set_eq_of_lt (a : α) {n} {l : List α} (h : n < length l) :
  (set l n a).get? n = some a := by rw [get?_set_eq, get?_eq_get h]; rfl

theorem get?_set_ne (a : α) {m n} (l : List α) (h : m ≠ n) : (set l m a).get? n = l.get? n := by
  simp only [set_eq_modifyNth, get?_modifyNth_ne _ _ h]

theorem get?_set (a : α) {m n} (l : List α) :
    (set l m a).get? n = if m = n then (fun _ => a) <$> l.get? n else l.get? n := by
  by_cases m = n <;> simp [*, get?_set_eq, get?_set_ne]

theorem get?_set_of_lt (a : α) {m n} (l : List α) (h : n < length l) :
    (set l m a).get? n = if m = n then some a else l.get? n := by
  simp [get?_set, get?_eq_get h]

theorem get?_set_of_lt' (a : α) {m n} (l : List α) (h : m < length l) :
    (set l m a).get? n = if m = n then some a else l.get? n := by
  simp [get?_set]; split <;> subst_vars <;> simp [*, get?_eq_get h]

@[simp] theorem set_nil (n : Nat) (a : α) : [].set n a = [] := rfl

@[simp] theorem set_succ (x : α) (xs : List α) (n : Nat) (a : α) :
  (x :: xs).set n.succ a = x :: xs.set n a := rfl

theorem set_comm (a b : α) : ∀ {n m : Nat} (l : List α), n ≠ m →
    (l.set n a).set m b = (l.set m b).set n a
  | _, _, [], _ => by simp
  | n+1, 0, _ :: _, _ => by simp [set]
  | 0, m+1, _ :: _, _ => by simp [set]
  | n+1, m+1, x :: t, h =>
    congrArg _ <| set_comm a b t fun h' => h <| Nat.succ_inj'.mpr h'

theorem set_set (a b : α) : ∀ (l : List α) (n : Nat), (l.set n a).set n b = l.set n b
  | [], _ => by simp
  | _ :: _, 0 => by simp [set]
  | _ :: _, _+1 => by simp [set, set_set]

@[simp] theorem get_set_eq (l : List α) (i : Nat) (a : α) (h : i < (l.set i a).length) :
    (l.set i a).get ⟨i, h⟩ = a := by
  rw [← Option.some_inj, ← get?_eq_get, get?_set_eq, get?_eq_get] <;> simp_all

@[simp] theorem get_set_ne {l : List α} {i j : Nat} (h : i ≠ j) (a : α)
    (hj : j < (l.set i a).length) :
    (l.set i a).get ⟨j, hj⟩ = l.get ⟨j, by simp at hj; exact hj⟩ := by
  rw [← Option.some_inj, ← get?_eq_get, get?_set_ne _ _ h, get?_eq_get]

theorem get_set (a : α) {m n} (l : List α) (h) :
    (set l m a).get ⟨n, h⟩ = if m = n then a else l.get ⟨n, length_set .. ▸ h⟩ := by
  if h : m = n then subst m; simp else simp [h]

theorem mem_or_eq_of_mem_set : ∀ {l : List α} {n : Nat} {a b : α}, a ∈ l.set n b → a ∈ l ∨ a = b
  | _ :: _, 0, _, _, h => ((mem_cons ..).1 h).symm.imp_left (.tail _)
  | _ :: _, _+1, _, _, .head .. => .inl (.head ..)
  | _ :: _, _+1, _, _, .tail _ h => (mem_or_eq_of_mem_set h).imp_left (.tail _)

/-! ### remove nth -/

theorem length_removeNth : ∀ {l i}, i < length l → length (@removeNth α l i) = length l - 1
  | [], _, _ => rfl
  | _::_, 0, _ => by simp [removeNth]
  | x::xs, i+1, h => by
    have : i < length xs := Nat.lt_of_succ_lt_succ h
    simp [removeNth, ← Nat.add_one]
    rw [length_removeNth this, Nat.sub_add_cancel (Nat.lt_of_le_of_lt (Nat.zero_le _) this)]

/-! ### tail -/

@[simp] theorem length_tail (l : List α) : length (tail l) = length l - 1 := by cases l <;> rfl

/-! ### all / any -/

@[simp] theorem all_eq_true {l : List α} : l.all p ↔ ∀ x ∈ l, p x := by induction l <;> simp [*]

@[simp] theorem any_eq_true {l : List α} : l.any p ↔ ∃ x ∈ l, p x := by induction l <;> simp [*]

theorem all_eq_not_any_not (l : List α) (p : α → Bool) : l.all p = !l.any (fun c => !p c) := by
  rw [Bool.eq_iff_iff]; simp; rw [← Bool.not_eq_true, List.any_eq_true]; simp

@[simp] theorem contains_nil [BEq α] : ([] : List α).contains a = false := rfl

@[simp] theorem contains_cons [BEq α] :
    (a :: as : List α).contains x = (x == a || as.contains x) := by
  simp only [contains, elem]
  split <;> simp_all

theorem contains_eq_any_beq [BEq α] (l : List α) (a : α) : l.contains a = l.any (a == ·) := by
  induction l with simp | cons b l => cases a == b <;> simp [*]

/-! ### reverse -/

@[simp] theorem mem_reverseAux {x : α} : ∀ {as bs}, x ∈ reverseAux as bs ↔ x ∈ as ∨ x ∈ bs
  | [], _ => ⟨.inr, fun | .inr h => h⟩
  | a :: _, _ => by rw [reverseAux, mem_cons, or_assoc, or_left_comm, mem_reverseAux, mem_cons]

@[simp] theorem mem_reverse {x : α} {as : List α} : x ∈ reverse as ↔ x ∈ as := by simp [reverse]

/-! ### insert -/

section insert
variable [DecidableEq α]

@[simp] theorem insert_of_mem {l : List α} (h : a ∈ l) : l.insert a = l := by
  simp only [List.insert, if_pos h]

@[simp] theorem insert_of_not_mem {l : List α} (h : a ∉ l) : l.insert a = a :: l := by
  simp only [List.insert, if_neg h]

@[simp] theorem mem_insert_iff {l : List α} : a ∈ l.insert b ↔ a = b ∨ a ∈ l := by
  if h : b ∈ l then
    rw [insert_of_mem h]
    constructor; {apply Or.inr}
    intro
    | Or.inl h' => rw [h']; exact h
    | Or.inr h' => exact h'
  else rw [insert_of_not_mem h, mem_cons]

@[simp 1100] theorem mem_insert_self (a : α) (l : List α) : a ∈ l.insert a :=
  mem_insert_iff.2 (Or.inl rfl)

theorem mem_insert_of_mem {l : List α} (h : a ∈ l) : a ∈ l.insert b :=
  mem_insert_iff.2 (Or.inr h)

theorem eq_or_mem_of_mem_insert {l : List α} (h : a ∈ l.insert b) : a = b ∨ a ∈ l :=
  mem_insert_iff.1 h

@[simp] theorem length_insert_of_mem {l : List α} (h : a ∈ l) :
    length (l.insert a) = length l := by rw [insert_of_mem h]

@[simp] theorem length_insert_of_not_mem {l : List α} (h : a ∉ l) :
    length (l.insert a) = length l + 1 := by rw [insert_of_not_mem h]; rfl

end insert

/-! ### eraseP -/

@[simp] theorem eraseP_nil : [].eraseP p = [] := rfl

theorem eraseP_cons (a : α) (l : List α) :
    (a :: l).eraseP p = bif p a then l else a :: l.eraseP p := rfl

@[simp] theorem eraseP_cons_of_pos {l : List α} (p) (h : p a) : (a :: l).eraseP p = l := by
  simp [eraseP_cons, h]

@[simp] theorem eraseP_cons_of_neg {l : List α} (p) (h : ¬p a) :
    (a :: l).eraseP p = a :: l.eraseP p := by simp [eraseP_cons, h]

theorem eraseP_of_forall_not {l : List α} (h : ∀ a, a ∈ l → ¬p a) : l.eraseP p = l := by
  induction l with
  | nil => rfl
  | cons _ _ ih => simp [h _ (.head ..), ih (forall_mem_cons.1 h).2]

theorem exists_of_eraseP : ∀ {l : List α} {a} (al : a ∈ l) (pa : p a),
    ∃ a l₁ l₂, (∀ b ∈ l₁, ¬p b) ∧ p a ∧ l = l₁ ++ a :: l₂ ∧ l.eraseP p = l₁ ++ l₂
  | b :: l, a, al, pa =>
    if pb : p b then
      ⟨b, [], l, forall_mem_nil _, pb, by simp [pb]⟩
    else
      match al with
      | .head .. => nomatch pb pa
      | .tail _ al =>
        let ⟨c, l₁, l₂, h₁, h₂, h₃, h₄⟩ := exists_of_eraseP al pa
        ⟨c, b::l₁, l₂, (forall_mem_cons ..).2 ⟨pb, h₁⟩,
          h₂, by rw [h₃, cons_append], by simp [pb, h₄]⟩

theorem exists_or_eq_self_of_eraseP (p) (l : List α) :
    l.eraseP p = l ∨
    ∃ a l₁ l₂, (∀ b ∈ l₁, ¬p b) ∧ p a ∧ l = l₁ ++ a :: l₂ ∧ l.eraseP p = l₁ ++ l₂ :=
  if h : ∃ a ∈ l, p a then
    let ⟨_, ha, pa⟩ := h
    .inr (exists_of_eraseP ha pa)
  else
    .inl (eraseP_of_forall_not (h ⟨·, ·, ·⟩))

@[simp] theorem length_eraseP_of_mem (al : a ∈ l) (pa : p a) :
    length (l.eraseP p) = Nat.pred (length l) := by
  let ⟨_, l₁, l₂, _, _, e₁, e₂⟩ := exists_of_eraseP al pa
  rw [e₂]; simp [length_append, e₁]; rfl

theorem eraseP_append_left {a : α} (pa : p a) :
    ∀ {l₁ : List α} l₂, a ∈ l₁ → (l₁++l₂).eraseP p = l₁.eraseP p ++ l₂
  | x :: xs, l₂, h => by
    by_cases h' : p x <;> simp [h']
    rw [eraseP_append_left pa l₂ ((mem_cons.1 h).resolve_left (mt _ h'))]
    intro | rfl => exact pa

theorem eraseP_append_right :
    ∀ {l₁ : List α} l₂, (∀ b ∈ l₁, ¬p b) → eraseP p (l₁++l₂) = l₁ ++ l₂.eraseP p
  | [],      l₂, _ => rfl
  | x :: xs, l₂, h => by
    simp [(forall_mem_cons.1 h).1, eraseP_append_right _ (forall_mem_cons.1 h).2]

theorem eraseP_sublist (l : List α) : l.eraseP p <+ l := by
  match exists_or_eq_self_of_eraseP p l with
  | .inl h => rw [h]; apply Sublist.refl
  | .inr ⟨c, l₁, l₂, _, _, h₃, h₄⟩ => rw [h₄, h₃]; simp

theorem eraseP_subset (l : List α) : l.eraseP p ⊆ l := (eraseP_sublist l).subset

theorem Sublist.eraseP : l₁ <+ l₂ → l₁.eraseP p <+ l₂.eraseP p
  | .slnil => Sublist.refl _
  | .cons a s => by
    by_cases h : p a <;> simp [h]
    exacts [s.eraseP.trans (eraseP_sublist _), s.eraseP.cons _]
  | .cons₂ a s => by
    by_cases h : p a <;> simp [h]
    exacts [s, s.eraseP.cons₂ _]

theorem mem_of_mem_eraseP {l : List α} : a ∈ l.eraseP p → a ∈ l := (eraseP_subset _ ·)

@[simp] theorem mem_eraseP_of_neg {l : List α} (pa : ¬p a) : a ∈ l.eraseP p ↔ a ∈ l := by
  refine ⟨mem_of_mem_eraseP, fun al => ?_⟩
  match exists_or_eq_self_of_eraseP p l with
  | .inl h => rw [h]; assumption
  | .inr ⟨c, l₁, l₂, h₁, h₂, h₃, h₄⟩ =>
    rw [h₄]; rw [h₃] at al
    have : a ≠ c := fun h => (h ▸ pa).elim h₂
    simp [this] at al; simp [al]

theorem eraseP_map (f : β → α) : ∀ (l : List β), (map f l).eraseP p = map f (l.eraseP (p ∘ f))
  | [] => rfl
  | b::l => by by_cases h : p (f b) <;> simp [h, eraseP_map f l, eraseP_cons_of_pos]

@[simp] theorem extractP_eq_find?_eraseP
    (l : List α) : extractP p l = (find? p l, eraseP p l) := by
  let rec go (acc) : ∀ xs, l = acc.data ++ xs →
    extractP.go p l xs acc = (xs.find? p, acc.data ++ xs.eraseP p)
  | [] => fun h => by simp [extractP.go, find?, eraseP, h]
  | x::xs => by
    simp [extractP.go, find?, eraseP]; cases p x <;> simp
    · intro h; rw [go _ xs]; {simp}; simp [h]
  exact go #[] _ rfl

/-! ### erase -/

section erase
-- FIXME: this should use a `BEq` assumption
variable [DecidableEq α]

@[simp] theorem erase_nil (a : α) : [].erase a = [] := rfl

theorem erase_cons (a b : α) (l : List α) :
    (b :: l).erase a = if b = a then l else b :: l.erase a :=
  if h : b = a then by simp [List.erase, h]
  else by simp [List.erase, h, (beq_eq_false_iff_ne _ _).2 h]

@[simp] theorem erase_cons_head (a : α) (l : List α) : (a :: l).erase a = l := by
  simp [erase_cons]

@[simp] theorem erase_cons_tail {a b : α} (l : List α) (h : b ≠ a) :
    (b :: l).erase a = b :: l.erase a := by simp only [erase_cons, if_neg h]

theorem erase_eq_eraseP (a : α) : ∀ l : List α, l.erase a = l.eraseP (Eq a)
  | [] => rfl
  | b :: l => by
    if h : a = b then simp [h] else simp [h, Ne.symm h, erase_eq_eraseP a l]

theorem Sublist.erase (a : α) {l₁ l₂ : List α} (h : l₁ <+ l₂) : l₁.erase a <+ l₂.erase a := by
  simp [erase_eq_eraseP]; exact Sublist.eraseP h

theorem erase_of_not_mem {a : α} : ∀ {l : List α}, a ∉ l → l.erase a = l
  | [], _ => rfl
  | b :: l, h => by
    rw [mem_cons, not_or] at h
    rw [erase_cons, if_neg (Ne.symm h.1), erase_of_not_mem h.2]

theorem exists_erase_eq {a : α} {l : List α} (h : a ∈ l) :
    ∃ l₁ l₂, a ∉ l₁ ∧ l = l₁ ++ a :: l₂ ∧ l.erase a = l₁ ++ l₂ := by
  let ⟨_, l₁, l₂, h₁, e, h₂, h₃⟩ := exists_of_eraseP h (beq_self_eq_true _)
  rw [erase_eq_eraseP]; exact ⟨l₁, l₂, fun h => h₁ _ h (beq_self_eq_true _), eq_of_beq e ▸ h₂, h₃⟩

@[simp] theorem length_erase_of_mem {a : α} {l : List α} (h : a ∈ l) :
    length (l.erase a) = Nat.pred (length l) := by
  rw [erase_eq_eraseP]; exact length_eraseP_of_mem h (decide_eq_true rfl)

theorem erase_append_left {l₁ : List α} (l₂) (h : a ∈ l₁) :
    (l₁ ++ l₂).erase a = l₁.erase a ++ l₂ := by
  simp [erase_eq_eraseP]; exact eraseP_append_left (by exact decide_eq_true rfl) l₂ h

theorem erase_append_right {a : α} {l₁ : List α} (l₂ : List α) (h : a ∉ l₁) :
    (l₁ ++ l₂).erase a = (l₁ ++ l₂.erase a) := by
  rw [erase_eq_eraseP, erase_eq_eraseP, eraseP_append_right]
  intros b h' h''; rw [of_decide_eq_true h''] at h; exact h h'

theorem erase_sublist (a : α) (l : List α) : l.erase a <+ l :=
  erase_eq_eraseP a l ▸ eraseP_sublist l

theorem erase_subset (a : α) (l : List α) : l.erase a ⊆ l := (erase_sublist a l).subset

theorem sublist.erase (a : α) {l₁ l₂ : List α} (h : l₁ <+ l₂) : l₁.erase a <+ l₂.erase a := by
  simp only [erase_eq_eraseP]; exact h.eraseP

theorem mem_of_mem_erase {a b : α} {l : List α} (h : a ∈ l.erase b) : a ∈ l := erase_subset _ _ h

@[simp] theorem mem_erase_of_ne {a b : α} {l : List α} (ab : a ≠ b) : a ∈ l.erase b ↔ a ∈ l :=
  erase_eq_eraseP b l ▸ mem_eraseP_of_neg (mt of_decide_eq_true ab.symm)

theorem erase_comm (a b : α) (l : List α) : (l.erase a).erase b = (l.erase b).erase a := by
  if ab : a = b then rw [ab] else ?_
  if ha : a ∈ l then ?_ else
    simp only [erase_of_not_mem ha, erase_of_not_mem (mt mem_of_mem_erase ha)]
  if hb : b ∈ l then ?_ else
    simp only [erase_of_not_mem hb, erase_of_not_mem (mt mem_of_mem_erase hb)]
  match l, l.erase a, exists_erase_eq ha with
  | _, _, ⟨l₁, l₂, ha', rfl, rfl⟩ =>
    if h₁ : b ∈ l₁ then
      rw [erase_append_left _ h₁, erase_append_left _ h₁,
          erase_append_right _ (mt mem_of_mem_erase ha'), erase_cons_head]
    else
      rw [erase_append_right _ h₁, erase_append_right _ h₁, erase_append_right _ ha',
          erase_cons_tail _ ab, erase_cons_head]

end erase

/-! ### filter and partition -/

@[simp] theorem filter_nil (p : α → Bool) : filter p [] = [] := rfl

@[simp] theorem filter_cons_of_pos {p : α → Bool} {a : α} (l) (pa : p a) :
    filter p (a :: l) = a :: filter p l := by rw [filter, pa]

@[simp] theorem filter_cons_of_neg {p : α → Bool} {a : α} (l) (pa : ¬ p a) :
    filter p (a :: l) = filter p l := by rw [filter, eq_false_of_ne_true pa]

@[simp] theorem filter_append {p : α → Bool} :
    ∀ (l₁ l₂ : List α), filter p (l₁ ++ l₂) = filter p l₁ ++ filter p l₂
  | [], l₂ => rfl
  | a :: l₁, l₂ => by simp [filter]; split <;> simp [filter_append l₁]

@[simp] theorem filter_sublist {p : α → Bool} : ∀ (l : List α), filter p l <+ l
  | [] => .slnil
  | a :: l => by rw [filter]; split <;> simp [Sublist.cons, Sublist.cons₂, filter_sublist l]

theorem mem_filter : x ∈ filter p as ↔ x ∈ as ∧ p x := by
  induction as with
  | nil => simp [filter]
  | cons a as ih =>
    by_cases h : p a <;> simp [*, or_and_right]
    · exact or_congr_left (and_iff_left_of_imp fun | rfl => h).symm
    · exact (or_iff_right fun ⟨rfl, h'⟩ => h h').symm

@[simp] theorem partition_eq_filter_filter (p : α → Bool) (l : List α) :
    partition p l = (filter p l, filter (not ∘ p) l) := by simp [partition, aux] where
  aux : ∀ l {as bs}, partition.loop p l (as, bs) =
    (as.reverse ++ filter p l, bs.reverse ++ filter (not ∘ p) l)
  | [] => by simp [partition.loop, filter]
  | a :: l => by cases pa : p a <;> simp [partition.loop, pa, aux, filter, append_assoc]

theorem filter_congr' {p q : α → Bool} :
    ∀ {l : List α}, (∀ x ∈ l, p x ↔ q x) → filter p l = filter q l
  | [], _ => rfl
  | a :: l, h => by
    rw [forall_mem_cons] at h; by_cases pa : p a
    · simp [pa, h.1.1 pa, filter_congr' h.2]
    · simp [pa, mt h.1.2 pa, filter_congr' h.2]

/-! ### filterMap -/

@[simp] theorem filterMap_nil (f : α → Option β) : filterMap f [] = [] := rfl

@[simp] theorem filterMap_cons (f : α → Option β) (a : α) (l : List α) :
    filterMap f (a :: l) =
      match f a with
      | none => filterMap f l
      | some b => b :: filterMap f l := rfl

theorem filterMap_cons_none {f : α → Option β} (a : α) (l : List α) (h : f a = none) :
    filterMap f (a :: l) = filterMap f l := by simp only [filterMap, h]

theorem filterMap_cons_some (f : α → Option β) (a : α) (l : List α) {b : β} (h : f a = some b) :
    filterMap f (a :: l) = b :: filterMap f l := by simp only [filterMap, h]

theorem filterMap_append {α β : Type _} (l l' : List α) (f : α → Option β) :
    filterMap f (l ++ l') = filterMap f l ++ filterMap f l' := by
  induction l <;> simp; split <;> simp [*]

theorem filterMap_eq_map (f : α → β) : filterMap (some ∘ f) = map f := by
  funext l; induction l <;> simp [*]

theorem filterMap_eq_filter (p : α → Bool) :
    filterMap (Option.guard (p ·)) = filter p := by
  funext l
  induction l with
  | nil => rfl
  | cons a l IH => by_cases pa : p a <;> simp [Option.guard, pa, ← IH]

theorem filterMap_filterMap (f : α → Option β) (g : β → Option γ) (l : List α) :
    filterMap g (filterMap f l) = filterMap (fun x => (f x).bind g) l := by
  induction l with
  | nil => rfl
  | cons a l IH => cases h : f a <;> simp [*]

theorem map_filterMap (f : α → Option β) (g : β → γ) (l : List α) :
    map g (filterMap f l) = filterMap (fun x => (f x).map g) l := by
  simp only [← filterMap_eq_map, filterMap_filterMap, Option.map_eq_bind]

theorem filterMap_map (f : α → β) (g : β → Option γ) (l : List α) :
    filterMap g (map f l) = filterMap (g ∘ f) l := by
  rw [← filterMap_eq_map, filterMap_filterMap]; rfl

theorem filter_filterMap (f : α → Option β) (p : β → Bool) (l : List α) :
    filter p (filterMap f l) = filterMap (fun x => (f x).filter p) l := by
  rw [← filterMap_eq_filter, filterMap_filterMap]
  congr; funext x; cases f x <;> simp [Option.filter, Option.guard]

theorem filterMap_filter (p : α → Bool) (f : α → Option β) (l : List α) :
    filterMap f (filter p l) = filterMap (fun x => if p x then f x else none) l := by
  rw [← filterMap_eq_filter, filterMap_filterMap]
  congr; funext x; by_cases h : p x <;> simp [Option.guard, h]

@[simp] theorem filterMap_some (l : List α) : filterMap some l = l := by
  erw [filterMap_eq_map, map_id]

theorem map_filterMap_some_eq_filter_map_is_some (f : α → Option β) (l : List α) :
    (l.filterMap f).map some = (l.map f).filter fun b => b.isSome := by
  induction l <;> simp; split <;> simp [*]

@[simp] theorem mem_filterMap (f : α → Option β) (l : List α) {b : β} :
    b ∈ filterMap f l ↔ ∃ a, a ∈ l ∧ f a = some b := by
  induction l <;> simp; split <;> simp [*, eq_comm]

@[simp] theorem filterMap_join (f : α → Option β) (L : List (List α)) :
    filterMap f (join L) = join (map (filterMap f) L) := by
  induction L <;> simp [*, filterMap_append]

theorem map_filterMap_of_inv (f : α → Option β) (g : β → α) (H : ∀ x : α, (f x).map g = some x)
    (l : List α) : map g (filterMap f l) = l := by simp only [map_filterMap, H, filterMap_some]

theorem length_filter_le (p : α → Bool) (l : List α) :
    (l.filter p).length ≤ l.length := (filter_sublist _).length_le

theorem length_filterMap_le (f : α → Option β) (l : List α) :
    (filterMap f l).length ≤ l.length := by
  rw [← length_map _ some, map_filterMap_some_eq_filter_map_is_some, ← length_map _ f]
  apply length_filter_le

theorem Sublist.filterMap (f : α → Option β) (s : l₁ <+ l₂) : filterMap f l₁ <+ filterMap f l₂ := by
  induction s <;> simp <;> split <;> simp [*, cons, cons₂]

theorem Sublist.filter (p : α → Bool) {l₁ l₂} (s : l₁ <+ l₂) : filter p l₁ <+ filter p l₂ := by
  rw [← filterMap_eq_filter]; apply s.filterMap

theorem map_filter (f : β → α) (l : List β) : filter p (map f l) = map f (filter (p ∘ f) l) := by
  rw [← filterMap_eq_map, filter_filterMap, filterMap_filter]; rfl

@[simp] theorem filter_filter (q) : ∀ l, filter p (filter q l) = filter (fun a => p a ∧ q a) l
  | [] => rfl
  | a :: l => by by_cases hp : p a <;> by_cases hq : q a <;> simp [hp, hq, filter_filter _ l]

theorem filter_eq_nil {l} : filter p l = [] ↔ ∀ a ∈ l, ¬p a := by
  simp only [eq_nil_iff_forall_not_mem, mem_filter, not_and]

theorem filter_eq_self {l} : filter p l = l ↔ ∀ a ∈ l, p a := by
  induction l with simp
  | cons a l ih =>
    cases h : p a <;> simp [*]
    intro h; exact Nat.lt_irrefl _ (h ▸ length_filter_le p l)

theorem filter_length_eq_length {l} : (filter p l).length = l.length ↔ ∀ a ∈ l, p a :=
  Iff.trans ⟨l.filter_sublist.eq_of_length, congrArg length⟩ filter_eq_self

/-! ### find? -/

theorem find?_cons_of_pos (l) (h : p a) : find? p (a :: l) = some a :=
  by simp [find?, h]

theorem find?_cons_of_neg (l) (h : ¬p a) : find? p (a :: l) = find? p l :=
  by simp [find?, h]

theorem find?_eq_none : find? p l = none ↔ ∀ x ∈ l, ¬ p x := by
  induction l <;> simp [find?_cons]; split <;> simp [*]

theorem find?_some : ∀ {l}, find? p l = some a → p a
  | b :: l, H => by
    by_cases h : p b <;> simp [find?, h] at H
    · exact H ▸ h
    · exact find?_some H

@[simp] theorem mem_of_find?_eq_some : ∀ {l}, find? p l = some a → a ∈ l
  | b :: l, H => by
    by_cases h : p b <;> simp [find?, h] at H
    · exact H ▸ .head _
    · exact .tail _ (mem_of_find?_eq_some H)

/-! ### findSome? -/

theorem exists_of_findSome?_eq_some {l : List α} {f : α → Option β} (w : l.findSome? f = some b) :
    ∃ a, a ∈ l ∧ f a = b := by
  induction l with
  | nil => simp_all
  | cons h l ih =>
    simp_all only [findSome?_cons, mem_cons, exists_eq_or_imp]
    split at w <;> simp_all

/-! ### findIdx -/

@[simp] theorem findIdx_nil {α : Type _} (p : α → Bool) : [].findIdx p = 0 := rfl

theorem findIdx_cons (p : α → Bool) (b : α) (l : List α) :
    (b :: l).findIdx p = bif p b then 0 else (l.findIdx p) + 1 := by
  cases H : p b with
  | true => simp [H, findIdx, findIdx.go]
  | false => simp [H, findIdx, findIdx.go, findIdx_go_succ]
where
  findIdx_go_succ (p : α → Bool) (l : List α) (n : Nat) :
      List.findIdx.go p l (n + 1) = (findIdx.go p l n) + 1 := by
    cases l with
    | nil => unfold findIdx.go; exact Nat.succ_eq_add_one n
    | cons head tail =>
      unfold findIdx.go
      cases p head <;> simp only [cond_false, cond_true]
      exact findIdx_go_succ p tail (n + 1)

theorem findIdx_of_get?_eq_some {xs : List α} (w : xs.get? (xs.findIdx p) = some y) : p y := by
  induction xs with
  | nil => simp_all
  | cons x xs ih => by_cases h : p x <;> simp_all [findIdx_cons]

theorem findIdx_get {xs : List α} {w : xs.findIdx p < xs.length} :
    p (xs.get ⟨xs.findIdx p, w⟩) :=
  xs.findIdx_of_get?_eq_some (get?_eq_get w)

theorem findIdx_lt_length_of_exists {xs : List α} (h : ∃ x ∈ xs, p x) :
    xs.findIdx p < xs.length := by
  induction xs with
  | nil => simp_all
  | cons x xs ih =>
    by_cases p x
    · simp_all only [forall_exists_index, and_imp, mem_cons, exists_eq_or_imp, true_or,
        findIdx_cons, cond_true, length_cons]
      apply Nat.succ_pos
    · simp_all [findIdx_cons]
      refine Nat.succ_lt_succ ?_
      obtain ⟨x', m', h'⟩ := h
      exact ih x' m' h'

theorem findIdx_get?_eq_get_of_exists {xs : List α} (h : ∃ x ∈ xs, p x) :
    xs.get? (xs.findIdx p) = some (xs.get ⟨xs.findIdx p, xs.findIdx_lt_length_of_exists h⟩) :=
  get?_eq_get (findIdx_lt_length_of_exists h)

/-! ### pairwise -/

theorem Pairwise.sublist : l₁ <+ l₂ → l₂.Pairwise R → l₁.Pairwise R
  | .slnil, h => h
  | .cons _ s, .cons _ h₂ => h₂.sublist s
  | .cons₂ _ s, .cons h₁ h₂ => (h₂.sublist s).cons fun _ h => h₁ _ (s.subset h)

theorem pairwise_map {l : List α} :
    (l.map f).Pairwise R ↔ l.Pairwise fun a b => R (f a) (f b) := by
  induction l
  . simp
  . simp only [map, pairwise_cons, forall_mem_map_iff, *]

theorem pairwise_append {l₁ l₂ : List α} :
    (l₁ ++ l₂).Pairwise R ↔ l₁.Pairwise R ∧ l₂.Pairwise R ∧ ∀ a ∈ l₁, ∀ b ∈ l₂, R a b := by
  induction l₁ <;> simp [*, or_imp, forall_and, and_assoc, and_left_comm]

theorem pairwise_reverse {l : List α} :
    l.reverse.Pairwise R ↔ l.Pairwise (fun a b => R b a) := by
  induction l <;> simp [*, pairwise_append, and_comm]

theorem Pairwise.imp {α R S} (H : ∀ {a b}, R a b → S a b) :
    ∀ {l : List α}, l.Pairwise R → l.Pairwise S
  | _, .nil => .nil
  | _, .cons h₁ h₂ => .cons (H ∘ h₁ ·) (h₂.imp H)

/-! ### replaceF -/

theorem replaceF_nil : [].replaceF p = [] := rfl

theorem replaceF_cons (a : α) (l : List α) :
    (a :: l).replaceF p = match p a with
      | none => a :: replaceF p l
      | some a' => a' :: l := rfl

theorem replaceF_cons_of_some {l : List α} (p) (h : p a = some a') :
    (a :: l).replaceF p = a' :: l := by
  simp [replaceF_cons, h]

theorem replaceF_cons_of_none {l : List α} (p) (h : p a = none) :
    (a :: l).replaceF p = a :: l.replaceF p := by simp [replaceF_cons, h]

theorem replaceF_of_forall_none {l : List α} (h : ∀ a, a ∈ l → p a = none) : l.replaceF p = l := by
  induction l with
  | nil => rfl
  | cons _ _ ih => simp [h _ (.head ..), ih (forall_mem_cons.1 h).2]

theorem exists_of_replaceF : ∀ {l : List α} {a a'} (al : a ∈ l) (pa : p a = some a'),
    ∃ a a' l₁ l₂,
      (∀ b ∈ l₁, p b = none) ∧ p a = some a' ∧ l = l₁ ++ a :: l₂ ∧ l.replaceF p = l₁ ++ a' :: l₂
  | b :: l, a, a', al, pa =>
    match pb : p b with
    | some b' => ⟨b, b', [], l, forall_mem_nil _, pb, by simp [pb]⟩
    | none =>
      match al with
      | .head .. => nomatch pb.symm.trans pa
      | .tail _ al =>
        let ⟨c, c', l₁, l₂, h₁, h₂, h₃, h₄⟩ := exists_of_replaceF al pa
        ⟨c, c', b::l₁, l₂, (forall_mem_cons ..).2 ⟨pb, h₁⟩,
          h₂, by rw [h₃, cons_append], by simp [pb, h₄]⟩

theorem exists_or_eq_self_of_replaceF (p) (l : List α) :
    l.replaceF p = l ∨ ∃ a a' l₁ l₂,
      (∀ b ∈ l₁, p b = none) ∧ p a = some a' ∧ l = l₁ ++ a :: l₂ ∧ l.replaceF p = l₁ ++ a' :: l₂ :=
  if h : ∃ a ∈ l, (p a).isSome then
    let ⟨_, ha, pa⟩ := h
    .inr (exists_of_replaceF ha (Option.get_mem pa))
  else
    .inl <| replaceF_of_forall_none fun a ha =>
      Option.not_isSome_iff_eq_none.1 fun h' => h ⟨a, ha, h'⟩

@[simp] theorem length_replaceF : length (replaceF f l) = length l := by
  induction l <;> simp [replaceF]; split <;> simp [*]

/-! ### disjoint -/

theorem disjoint_symm (d : Disjoint l₁ l₂) : Disjoint l₂ l₁ := fun _ i₂ i₁ => d i₁ i₂

theorem disjoint_comm : Disjoint l₁ l₂ ↔ Disjoint l₂ l₁ := ⟨disjoint_symm, disjoint_symm⟩

theorem disjoint_left : Disjoint l₁ l₂ ↔ ∀ ⦃a⦄, a ∈ l₁ → a ∉ l₂ := by simp [Disjoint]

theorem disjoint_right : Disjoint l₁ l₂ ↔ ∀ ⦃a⦄, a ∈ l₂ → a ∉ l₁ := disjoint_comm

theorem disjoint_iff_ne : Disjoint l₁ l₂ ↔ ∀ a ∈ l₁, ∀ b ∈ l₂, a ≠ b :=
  ⟨fun h _ al1 _ bl2 ab => h al1 (ab ▸ bl2), fun h _ al1 al2 => h _ al1 _ al2 rfl⟩

theorem disjoint_of_subset_left (ss : l₁ ⊆ l) (d : Disjoint l l₂) : Disjoint l₁ l₂ :=
  fun _ m => d (ss m)

theorem disjoint_of_subset_right (ss : l₂ ⊆ l) (d : Disjoint l₁ l) : Disjoint l₁ l₂ :=
  fun _ m m₁ => d m (ss m₁)

theorem disjoint_of_disjoint_cons_left {l₁ l₂} : Disjoint (a :: l₁) l₂ → Disjoint l₁ l₂ :=
disjoint_of_subset_left (subset_cons _ _)

theorem disjoint_of_disjoint_cons_right {l₁ l₂} : Disjoint l₁ (a :: l₂) → Disjoint l₁ l₂ :=
disjoint_of_subset_right (subset_cons _ _)

@[simp] theorem disjoint_nil_left (l : List α) : Disjoint [] l := fun a => (not_mem_nil a).elim

@[simp] theorem disjoint_nil_right (l : List α) : Disjoint l [] := by
  rw [disjoint_comm]; exact disjoint_nil_left _

@[simp 1100] theorem singleton_disjoint : Disjoint [a] l ↔ a ∉ l := by simp [Disjoint]

@[simp 1100] theorem disjoint_singleton : Disjoint l [a] ↔ a ∉ l := by
  rw [disjoint_comm, singleton_disjoint]

@[simp] theorem disjoint_append_left : Disjoint (l₁ ++ l₂) l ↔ Disjoint l₁ l ∧ Disjoint l₂ l := by
  simp [Disjoint, or_imp, forall_and]

@[simp] theorem disjoint_append_right : Disjoint l (l₁ ++ l₂) ↔ Disjoint l l₁ ∧ Disjoint l l₂ :=
  disjoint_comm.trans <| by rw [disjoint_append_left]; simp [disjoint_comm]

@[simp] theorem disjoint_cons_left : Disjoint (a::l₁) l₂ ↔ (a ∉ l₂) ∧ Disjoint l₁ l₂ :=
  (disjoint_append_left (l₁ := [a])).trans <| by simp [singleton_disjoint]

@[simp] theorem disjoint_cons_right : Disjoint l₁ (a :: l₂) ↔ (a ∉ l₁) ∧ Disjoint l₁ l₂ :=
  disjoint_comm.trans <| by rw [disjoint_cons_left]; simp [disjoint_comm]

theorem disjoint_of_disjoint_append_left_left (d : Disjoint (l₁ ++ l₂) l) : Disjoint l₁ l :=
  (disjoint_append_left.1 d).1

theorem disjoint_of_disjoint_append_left_right (d : Disjoint (l₁ ++ l₂) l) : Disjoint l₂ l :=
  (disjoint_append_left.1 d).2

theorem disjoint_of_disjoint_append_right_left (d : Disjoint l (l₁ ++ l₂)) : Disjoint l l₁ :=
  (disjoint_append_right.1 d).1

theorem disjoint_of_disjoint_append_right_right (d : Disjoint l (l₁ ++ l₂)) : Disjoint l l₂ :=
  (disjoint_append_right.1 d).2

/-! ### foldl / foldr -/

theorem foldl_map (f : β₁ → β₂) (g : α → β₂ → α) (l : List β₁) (init : α) :
    (l.map f).foldl g init = l.foldl (fun x y => g x (f y)) init := by
  induction l generalizing init <;> simp [*]

theorem foldr_map (f : α₁ → α₂) (g : α₂ → β → β) (l : List α₁) (init : β) :
    (l.map f).foldr g init = l.foldr (fun x y => g (f x) y) init := by
  induction l generalizing init <;> simp [*]

theorem foldl_hom (f : α₁ → α₂) (g₁ : α₁ → β → α₁) (g₂ : α₂ → β → α₂) (l : List β) (init : α₁)
    (H : ∀ x y, g₂ (f x) y = f (g₁ x y)) : l.foldl g₂ (f init) = f (l.foldl g₁ init) := by
  induction l generalizing init <;> simp [*, H]

theorem foldr_hom (f : β₁ → β₂) (g₁ : α → β₁ → β₁) (g₂ : α → β₂ → β₂) (l : List α) (init : β₁)
    (H : ∀ x y, g₂ x (f y) = f (g₁ x y)) : l.foldr g₂ (f init) = f (l.foldr g₁ init) := by
  induction l <;> simp [*, H]

/-! ### union -/

section union

variable [DecidableEq α]

theorem union_def [DecidableEq α] (l₁ l₂ : List α)  : l₁ ∪ l₂ = foldr .insert l₂ l₁ := rfl

@[simp] theorem nil_union (l : List α) : nil ∪ l = l := by simp [List.union_def, foldr]

@[simp] theorem cons_union (a : α) (l₁ l₂ : List α) :
    (a :: l₁) ∪ l₂ = (l₁ ∪ l₂).insert a := by simp [List.union_def, foldr]

@[simp] theorem mem_union_iff [DecidableEq α] {x : α} {l₁ l₂ : List α} :
    x ∈ l₁ ∪ l₂ ↔ x ∈ l₁ ∨ x ∈ l₂ := by induction l₁ <;> simp [*, or_assoc]

end union

/-! ### inter -/

theorem inter_def [DecidableEq α] (l₁ l₂ : List α)  : l₁ ∩ l₂ = filter (· ∈ l₂) l₁ := rfl

@[simp] theorem mem_inter_iff [DecidableEq α] {x : α} {l₁ l₂ : List α} :
    x ∈ l₁ ∩ l₂ ↔ x ∈ l₁ ∧ x ∈ l₂ := by
  cases l₁ <;> simp [List.inter_def, mem_filter]

/-! ### product -/

/-- List.prod satisfies a specification of cartesian product on lists. -/
theorem pair_mem_product {xs : List α} {ys : List β} {x : α} {y : β} :
    (x, y) ∈ product xs ys ↔ x ∈ xs ∧ y ∈ ys := by
  simp only [product, and_imp, exists_prop, mem_map, Prod.mk.injEq,
    exists_eq_right_right, mem_bind, iff_self]

/-! ### leftpad -/

/-- The length of the List returned by `List.leftpad n a l` is equal
  to the larger of `n` and `l.length` -/
theorem leftpad_length (n : Nat) (a : α) (l : List α) :
    (leftpad n a l).length = max n l.length := by
  simp only [leftpad, length_append, length_replicate, Nat.sub_add_eq_max]

theorem leftpad_prefix (n : Nat) (a : α) (l : List α) :
    IsPrefix (replicate (n - length l) a) (leftpad n a l) := by
  simp only [IsPrefix, leftpad]
  exact Exists.intro l rfl

theorem leftpad_suffix (n : Nat) (a : α) (l : List α) : IsSuffix l (leftpad n a l) := by
  simp only [IsSuffix, leftpad]
  exact Exists.intro (replicate (n - length l) a) rfl

/-! ### monadic operations -/

-- we use ForIn.forIn as the simp normal form
@[simp] theorem forIn_eq_forIn [Monad m] : @List.forIn α β m _ = forIn := rfl

theorem forIn_eq_bindList [Monad m] [LawfulMonad m]
    (f : α → β → m (ForInStep β)) (l : List α) (init : β) :
    forIn l init f = ForInStep.run <$> (ForInStep.yield init).bindList f l := by
  induction l generalizing init <;> simp [*, map_eq_pure_bind]
  congr; ext (b | b) <;> simp

@[simp] theorem forM_append [Monad m] [LawfulMonad m] (l₁ l₂ : List α) (f : α → m PUnit) :
    (l₁ ++ l₂).forM f = (do l₁.forM f; l₂.forM f) := by induction l₁ <;> simp [*]

/-! ### diff -/

section Diff
-- TODO: theorems about `BEq`
variable [DecidableEq α]

@[simp] theorem diff_nil (l : List α) : l.diff [] = l := rfl

@[simp] theorem diff_cons (l₁ l₂ : List α) (a : α) : l₁.diff (a :: l₂) = (l₁.erase a).diff l₂ := by
  simp [List.diff]; split <;> simp [*, erase_of_not_mem]

theorem diff_cons_right (l₁ l₂ : List α) (a : α) : l₁.diff (a :: l₂) = (l₁.diff l₂).erase a := by
  apply Eq.symm; induction l₂ generalizing l₁ <;> simp [erase_comm, *]

theorem diff_erase (l₁ l₂ : List α) (a : α) : (l₁.diff l₂).erase a = (l₁.erase a).diff l₂ := by
  rw [← diff_cons_right, diff_cons]

@[simp] theorem nil_diff (l : List α) : [].diff l = [] := by
  induction l <;> simp [*, erase_of_not_mem]

theorem cons_diff (a : α) (l₁ l₂ : List α) :
    (a :: l₁).diff l₂ = if a ∈ l₂ then l₁.diff (l₂.erase a) else a :: l₁.diff l₂ := by
  induction l₂ generalizing l₁ with
  | nil => rfl
  | cons b l₂ ih => by_cases h : a = b <;> simp [*, eq_comm]

theorem cons_diff_of_mem {a : α} {l₂ : List α} (h : a ∈ l₂) (l₁ : List α) :
    (a :: l₁).diff l₂ = l₁.diff (l₂.erase a) := by rw [cons_diff, if_pos h]

theorem cons_diff_of_not_mem {a : α} {l₂ : List α} (h : a ∉ l₂) (l₁ : List α) :
    (a :: l₁).diff l₂ = a :: l₁.diff l₂ := by rw [cons_diff, if_neg h]

theorem diff_eq_foldl : ∀ l₁ l₂ : List α, l₁.diff l₂ = foldl List.erase l₁ l₂
  | _, [] => rfl
  | l₁, a :: l₂ => (diff_cons l₁ l₂ a).trans (diff_eq_foldl _ _)

@[simp] theorem diff_append (l₁ l₂ l₃ : List α) : l₁.diff (l₂ ++ l₃) = (l₁.diff l₂).diff l₃ := by
  simp only [diff_eq_foldl, foldl_append]

theorem diff_sublist : ∀ l₁ l₂ : List α, l₁.diff l₂ <+ l₁
  | _, [] => .refl _
  | l₁, a :: l₂ =>
    calc
      l₁.diff (a :: l₂) = (l₁.erase a).diff l₂ := diff_cons ..
      _ <+ l₁.erase a := diff_sublist ..
      _ <+ l₁ := erase_sublist ..

theorem diff_subset (l₁ l₂ : List α) : l₁.diff l₂ ⊆ l₁ := (diff_sublist ..).subset

theorem mem_diff_of_mem {a : α} : ∀ {l₁ l₂ : List α}, a ∈ l₁ → a ∉ l₂ → a ∈ l₁.diff l₂
  | _, [], h₁, _ => h₁
  | l₁, b :: l₂, h₁, h₂ => by
    rw [diff_cons]
    exact mem_diff_of_mem ((mem_erase_of_ne <| ne_of_not_mem_cons h₂).2 h₁) (mt (.tail _) h₂)

theorem Sublist.diff_right : ∀ {l₁ l₂ l₃ : List α}, l₁ <+ l₂ → l₁.diff l₃ <+ l₂.diff l₃
  | _,  _, [], h => h
  | l₁, l₂, a :: l₃, h => by simp only [diff_cons, (h.erase _).diff_right]

theorem Sublist.erase_diff_erase_sublist {a : α} :
    ∀ {l₁ l₂ : List α}, l₁ <+ l₂ → (l₂.erase a).diff (l₁.erase a) <+ l₂.diff l₁
  | [], l₂, _ => erase_sublist _ _
  | b :: l₁, l₂, h => by
    if heq : b = a then
      simp [heq]
    else
      simp [heq, erase_comm a]
      exact (erase_cons_head b _ ▸ h.erase b).erase_diff_erase_sublist

end Diff

/-! ### prefix, suffix, infix -/

@[simp] theorem prefix_append (l₁ l₂ : List α) : l₁ <+: l₁ ++ l₂ := ⟨l₂, rfl⟩

@[simp] theorem suffix_append (l₁ l₂ : List α) : l₂ <:+ l₁ ++ l₂ := ⟨l₁, rfl⟩

theorem infix_append (l₁ l₂ l₃ : List α) : l₂ <:+: l₁ ++ l₂ ++ l₃ := ⟨l₁, l₃, rfl⟩

@[simp] theorem infix_append' (l₁ l₂ l₃ : List α) : l₂ <:+: l₁ ++ (l₂ ++ l₃) := by
  rw [← List.append_assoc]; apply infix_append

theorem IsPrefix.isInfix : l₁ <+: l₂ → l₁ <:+: l₂ := fun ⟨t, h⟩ => ⟨[], t, h⟩

theorem IsSuffix.isInfix : l₁ <:+ l₂ → l₁ <:+: l₂ := fun ⟨t, h⟩ => ⟨t, [], by rw [h, append_nil]⟩

theorem nil_prefix (l : List α) : [] <+: l := ⟨l, rfl⟩

theorem nil_suffix (l : List α) : [] <:+ l := ⟨l, append_nil _⟩

theorem nil_infix (l : List α) : [] <:+: l := (nil_prefix _).isInfix

theorem prefix_refl (l : List α) : l <+: l := ⟨[], append_nil _⟩

theorem suffix_refl (l : List α) : l <:+ l := ⟨[], rfl⟩

theorem infix_refl (l : List α) : l <:+: l := (prefix_refl l).isInfix

@[simp] theorem suffix_cons (a : α) : ∀ l, l <:+ a :: l := suffix_append [a]

theorem infix_cons : l₁ <:+: l₂ → l₁ <:+: a :: l₂ := fun ⟨L₁, L₂, h⟩ => ⟨a :: L₁, L₂, h ▸ rfl⟩

theorem infix_concat : l₁ <:+: l₂ → l₁ <:+: concat l₂ a := fun ⟨L₁, L₂, h⟩ =>
  ⟨L₁, concat L₂ a, by simp [← h, concat_eq_append, append_assoc]⟩

theorem IsPrefix.trans : ∀ {l₁ l₂ l₃ : List α}, l₁ <+: l₂ → l₂ <+: l₃ → l₁ <+: l₃
  | _, _, _, ⟨r₁, rfl⟩, ⟨r₂, rfl⟩ => ⟨r₁ ++ r₂, (append_assoc _ _ _).symm⟩

theorem IsSuffix.trans : ∀ {l₁ l₂ l₃ : List α}, l₁ <:+ l₂ → l₂ <:+ l₃ → l₁ <:+ l₃
  | _, _, _, ⟨l₁, rfl⟩, ⟨l₂, rfl⟩ => ⟨l₂ ++ l₁, append_assoc _ _ _⟩

theorem IsInfix.trans : ∀ {l₁ l₂ l₃ : List α}, l₁ <:+: l₂ → l₂ <:+: l₃ → l₁ <:+: l₃
  | l, _, _, ⟨l₁, r₁, rfl⟩, ⟨l₂, r₂, rfl⟩ => ⟨l₂ ++ l₁, r₁ ++ r₂, by simp only [append_assoc]⟩

protected theorem IsInfix.sublist : l₁ <:+: l₂ → l₁ <+ l₂
  | ⟨_, _, h⟩ => h ▸ (sublist_append_right ..).trans (sublist_append_left ..)

protected theorem IsInfix.subset (hl : l₁ <:+: l₂) : l₁ ⊆ l₂ :=
  hl.sublist.subset

protected theorem IsPrefix.sublist (h : l₁ <+: l₂) : l₁ <+ l₂ :=
  h.isInfix.sublist

protected theorem IsPrefix.subset (hl : l₁ <+: l₂) : l₁ ⊆ l₂ :=
  hl.sublist.subset

protected theorem IsSuffix.sublist (h : l₁ <:+ l₂) : l₁ <+ l₂ :=
  h.isInfix.sublist

protected theorem IsSuffix.subset (hl : l₁ <:+ l₂) : l₁ ⊆ l₂ :=
  hl.sublist.subset

@[simp] theorem reverse_suffix : reverse l₁ <:+ reverse l₂ ↔ l₁ <+: l₂ :=
  ⟨fun ⟨r, e⟩ => ⟨reverse r, by rw [← reverse_reverse l₁, ← reverse_append, e, reverse_reverse]⟩,
   fun ⟨r, e⟩ => ⟨reverse r, by rw [← reverse_append, e]⟩⟩

@[simp] theorem reverse_prefix : reverse l₁ <+: reverse l₂ ↔ l₁ <:+ l₂ := by
  rw [← reverse_suffix]; simp only [reverse_reverse]

@[simp] theorem reverse_infix : reverse l₁ <:+: reverse l₂ ↔ l₁ <:+: l₂ := by
  refine ⟨fun ⟨s, t, e⟩ => ⟨reverse t, reverse s, ?_⟩, fun ⟨s, t, e⟩ => ⟨reverse t, reverse s, ?_⟩⟩
  · rw [← reverse_reverse l₁, append_assoc, ← reverse_append, ← reverse_append, e,
      reverse_reverse]
  · rw [append_assoc, ← reverse_append, ← reverse_append, e]

theorem IsInfix.length_le (h : l₁ <:+: l₂) : l₁.length ≤ l₂.length :=
  h.sublist.length_le

theorem IsPrefix.length_le (h : l₁ <+: l₂) : l₁.length ≤ l₂.length :=
  h.sublist.length_le

theorem IsSuffix.length_le (h : l₁ <:+ l₂) : l₁.length ≤ l₂.length :=
  h.sublist.length_le

@[simp] theorem infix_nil : l <:+: [] ↔ l = [] := ⟨(sublist_nil.1 ·.sublist), (· ▸ infix_refl _)⟩

@[simp] theorem prefix_nil : l <+: [] ↔ l = [] := ⟨(sublist_nil.1 ·.sublist), (· ▸ prefix_refl _)⟩

@[simp] theorem suffix_nil : l <:+ [] ↔ l = [] := ⟨(sublist_nil.1 ·.sublist), (· ▸ suffix_refl _)⟩

theorem infix_iff_prefix_suffix (l₁ l₂ : List α) : l₁ <:+: l₂ ↔ ∃ t, l₁ <+: t ∧ t <:+ l₂ :=
  ⟨fun ⟨_, t, e⟩ => ⟨l₁ ++ t, ⟨_, rfl⟩, e ▸ append_assoc .. ▸ ⟨_, rfl⟩⟩,
    fun ⟨_, ⟨t, rfl⟩, s, e⟩ => ⟨s, t, append_assoc .. ▸ e⟩⟩

theorem IsInfix.eq_of_length (h : l₁ <:+: l₂) : l₁.length = l₂.length → l₁ = l₂ :=
  h.sublist.eq_of_length

theorem IsPrefix.eq_of_length (h : l₁ <+: l₂) : l₁.length = l₂.length → l₁ = l₂ :=
  h.sublist.eq_of_length

theorem IsSuffix.eq_of_length (h : l₁ <:+ l₂) : l₁.length = l₂.length → l₁ = l₂ :=
  h.sublist.eq_of_length

theorem prefix_of_prefix_length_le :
    ∀ {l₁ l₂ l₃ : List α}, l₁ <+: l₃ → l₂ <+: l₃ → length l₁ ≤ length l₂ → l₁ <+: l₂
  | [], l₂, _, _, _, _ => nil_prefix _
  | a :: l₁, b :: l₂, _, ⟨r₁, rfl⟩, ⟨r₂, e⟩, ll => by
    injection e with _ e'; subst b
    rcases prefix_of_prefix_length_le ⟨_, rfl⟩ ⟨_, e'⟩ (le_of_succ_le_succ ll) with ⟨r₃, rfl⟩
    exact ⟨r₃, rfl⟩

theorem prefix_or_prefix_of_prefix (h₁ : l₁ <+: l₃) (h₂ : l₂ <+: l₃) : l₁ <+: l₂ ∨ l₂ <+: l₁ :=
  (Nat.le_total (length l₁) (length l₂)).imp (prefix_of_prefix_length_le h₁ h₂)
    (prefix_of_prefix_length_le h₂ h₁)

theorem suffix_of_suffix_length_le
    (h₁ : l₁ <:+ l₃) (h₂ : l₂ <:+ l₃) (ll : length l₁ ≤ length l₂) : l₁ <:+ l₂ :=
  reverse_prefix.1 <|
    prefix_of_prefix_length_le (reverse_prefix.2 h₁) (reverse_prefix.2 h₂) (by simp [ll])

theorem suffix_or_suffix_of_suffix (h₁ : l₁ <:+ l₃) (h₂ : l₂ <:+ l₃) : l₁ <:+ l₂ ∨ l₂ <:+ l₁ :=
  (prefix_or_prefix_of_prefix (reverse_prefix.2 h₁) (reverse_prefix.2 h₂)).imp reverse_prefix.1
    reverse_prefix.1

theorem suffix_cons_iff : l₁ <:+ a :: l₂ ↔ l₁ = a :: l₂ ∨ l₁ <:+ l₂ := by
  constructor
  · rintro ⟨⟨hd, tl⟩, hl₃⟩
    · exact Or.inl hl₃
    · simp only [cons_append] at hl₃
      injection hl₃ with _ hl₄
      exact Or.inr ⟨_, hl₄⟩
  · rintro (rfl | hl₁)
    · exact (a :: l₂).suffix_refl
    · exact hl₁.trans (l₂.suffix_cons _)

theorem infix_cons_iff : l₁ <:+: a :: l₂ ↔ l₁ <+: a :: l₂ ∨ l₁ <:+: l₂ := by
  constructor
  · rintro ⟨⟨hd, tl⟩, t, hl₃⟩
    · exact Or.inl ⟨t, hl₃⟩
    · simp only [cons_append] at hl₃
      injection hl₃ with _ hl₄
      exact Or.inr ⟨_, t, hl₄⟩
  · rintro (h | hl₁)
    · exact h.isInfix
    · exact infix_cons hl₁

theorem infix_of_mem_join : ∀ {L : List (List α)}, l ∈ L → l <:+: join L
  | l' :: _, h =>
    match h with
    | List.Mem.head .. => infix_append [] _ _
    | List.Mem.tail _ hlMemL =>
      IsInfix.trans (infix_of_mem_join hlMemL) <| (suffix_append _ _).isInfix

theorem prefix_append_right_inj (l) : l ++ l₁ <+: l ++ l₂ ↔ l₁ <+: l₂ :=
  exists_congr fun r => by rw [append_assoc, append_right_inj]

theorem prefix_cons_inj (a) : a :: l₁ <+: a :: l₂ ↔ l₁ <+: l₂ :=
  prefix_append_right_inj [a]

theorem take_prefix (n) (l : List α) : take n l <+: l :=
  ⟨_, take_append_drop _ _⟩

theorem drop_suffix (n) (l : List α) : drop n l <:+ l :=
  ⟨_, take_append_drop _ _⟩

theorem take_sublist (n) (l : List α) : take n l <+ l :=
  (take_prefix n l).sublist

theorem drop_sublist (n) (l : List α) : drop n l <+ l :=
  (drop_suffix n l).sublist

theorem take_subset (n) (l : List α) : take n l ⊆ l :=
  (take_sublist n l).subset

theorem drop_subset (n) (l : List α) : drop n l ⊆ l :=
  (drop_sublist n l).subset

theorem mem_of_mem_take {l : List α} (h : a ∈ l.take n) : a ∈ l :=
  take_subset n l h

theorem IsPrefix.filter (p : α → Bool) ⦃l₁ l₂ : List α⦄ (h : l₁ <+: l₂) :
    l₁.filter p <+: l₂.filter p := by
  obtain ⟨xs, rfl⟩ := h
  rw [filter_append]; apply prefix_append

theorem IsSuffix.filter (p : α → Bool) ⦃l₁ l₂ : List α⦄ (h : l₁ <:+ l₂) :
    l₁.filter p <:+ l₂.filter p := by
  obtain ⟨xs, rfl⟩ := h
  rw [filter_append]; apply suffix_append

theorem IsInfix.filter (p : α → Bool) ⦃l₁ l₂ : List α⦄ (h : l₁ <:+: l₂) :
    l₁.filter p <:+: l₂.filter p := by
  obtain ⟨xs, ys, rfl⟩ := h
  rw [filter_append, filter_append]; apply infix_append _

theorem mem_of_mem_drop {n} {l : List α} (h : a ∈ l.drop n) : a ∈ l := drop_subset _ _ h

theorem disjoint_take_drop : ∀ {l : List α}, l.Nodup → m ≤ n → Disjoint (l.take m) (l.drop n)
  | [], _, _ => by simp
  | x :: xs, hl, h => by
    cases m <;> cases n <;> simp only [disjoint_cons_left, mem_cons, disjoint_cons_right,
      drop, true_or, eq_self_iff_true, not_true, false_and, not_mem_nil, disjoint_nil_left, take]
    · case succ.zero => cases h
    · cases hl with | cons h₀ h₁ =>
      refine ⟨fun h => h₀ _ (mem_of_mem_drop h) rfl, ?_⟩
      exact disjoint_take_drop h₁ (Nat.le_of_succ_le_succ h)

/-! ### takeWhile and dropWhile -/

@[simp] theorem takeWhile_append_dropWhile (p : α → Bool) :
    ∀ (l : List α), takeWhile p l ++ dropWhile p l = l
  | [] => rfl
  | x :: xs => by simp [takeWhile, dropWhile]; cases p x <;> simp [takeWhile_append_dropWhile p xs]

/-! ### Chain -/

--Porting note: attribute in Lean3, but not in Lean4 Std so added here instead
attribute [simp] Chain.nil

@[simp]
theorem chain_cons {a b : α} {l : List α} : Chain R a (b :: l) ↔ R a b ∧ Chain R b l :=
  ⟨fun p => by cases p with | cons n p => exact ⟨n, p⟩,
   fun ⟨n, p⟩ => p.cons n⟩

theorem rel_of_chain_cons {a b : α} {l : List α} (p : Chain R a (b :: l)) : R a b :=
  (chain_cons.1 p).1

theorem chain_of_chain_cons {a b : α} {l : List α} (p : Chain R a (b :: l)) : Chain R b l :=
  (chain_cons.1 p).2

theorem Chain.imp' {R S : α → α → Prop} (HRS : ∀ ⦃a b⦄, R a b → S a b) {a b : α}
    (Hab : ∀ ⦃c⦄, R a c → S b c) {l : List α} (p : Chain R a l) : Chain S b l := by
  induction p generalizing b with
  | nil => constructor
  | cons r _ ih =>
    constructor
    · exact Hab r
    · exact ih (@HRS _)

theorem Chain.imp {R S : α → α → Prop} (H : ∀ a b, R a b → S a b) {a : α} {l : List α}
    (p : Chain R a l) : Chain S a l :=
  p.imp' H (H a)

protected theorem Pairwise.chain (p : Pairwise R (a :: l)) : Chain R a l := by
  let ⟨r, p'⟩ := pairwise_cons.1 p; clear p
  induction p' generalizing a with
  | nil => exact Chain.nil
  | @cons b l r' _ IH =>
    simp only [chain_cons, forall_mem_cons] at r
    exact chain_cons.2 ⟨r.1, IH r'⟩

/-! ### range', range -/

@[simp] theorem length_range' (s step) : ∀ n : Nat, length (range' s n step) = n
  | 0 => rfl
  | _ + 1 => congrArg succ (length_range' _ _ _)

@[simp] theorem range'_eq_nil : range' s n step = [] ↔ n = 0 := by
  rw [← length_eq_zero, length_range']

theorem mem_range' : ∀{n}, m ∈ range' s n step ↔ ∃ i < n, m = s + step * i
  | 0 => by simp [range', Nat.not_lt_zero]
  | n + 1 => by
    have h (i) : i ≤ n ↔ i = 0 ∨ ∃ j, i = succ j ∧ j < n := by cases i <;> simp [Nat.succ_le]
    simp [range', mem_range', Nat.lt_succ, h]; simp only [← exists_and_right, and_assoc]
    rw [exists_comm]; simp [Nat.mul_succ, Nat.add_assoc, Nat.add_comm]

@[simp] theorem mem_range'_1 : m ∈ range' s n ↔ s ≤ m ∧ m < s + n := by
  simp [mem_range']; exact ⟨
    fun ⟨i, h, e⟩ => e ▸ ⟨Nat.le_add_right .., Nat.add_lt_add_left h _⟩,
    fun ⟨h₁, h₂⟩ => ⟨m - s, Nat.sub_lt_left_of_lt_add h₁ h₂, (Nat.add_sub_cancel' h₁).symm⟩⟩

theorem map_add_range' (a) : ∀ s n step, map (a + ·) (range' s n step) = range' (a + s) n step
  | _, 0, _ => rfl
  | s, n + 1, step => by simp [range', map_add_range' _ (s + step) n step, Nat.add_assoc]

theorem map_sub_range' (a s n : Nat) (h : a ≤ s) :
    map (· - a) (range' s n step) = range' (s - a) n step := by
  conv => lhs; rw [← Nat.add_sub_cancel' h]
  rw [← map_add_range', map_map, (?_ : _∘_ = _), map_id]
  funext x; apply Nat.add_sub_cancel_left

theorem chain_succ_range' : ∀ s n step : Nat,
    Chain (fun a b => b = a + step) s (range' (s + step) n step)
  | _, 0, _ => Chain.nil
  | s, n + 1, step => (chain_succ_range' (s + step) n step).cons rfl

theorem chain_lt_range' (s n : Nat) {step} (h : 0 < step) :
    Chain (· < ·) s (range' (s + step) n step) :=
  (chain_succ_range' s n step).imp fun _ _ e => e.symm ▸ Nat.lt_add_of_pos_right h

theorem range'_append : ∀ s m n step : Nat,
    range' s m step ++ range' (s + step * m) n step = range' s (n + m) step
  | s, 0, n, step => rfl
  | s, m + 1, n, step => by
    simpa [range', Nat.mul_succ, Nat.add_assoc, Nat.add_comm]
      using range'_append (s + step) m n step

@[simp] theorem range'_append_1 (s m n : Nat) :
    range' s m ++ range' (s + m) n = range' s (n + m) := by simpa using range'_append s m n 1

theorem range'_sublist_right {s m n : Nat} : range' s m step <+ range' s n step ↔ m ≤ n :=
  ⟨fun h => by simpa only [length_range'] using h.length_le,
   fun h => by rw [← Nat.sub_add_cancel h, ← range'_append]; apply sublist_append_left⟩

theorem range'_subset_right {s m n : Nat} (step0 : 0 < step) :
    range' s m step ⊆ range' s n step ↔ m ≤ n := by
  refine ⟨fun h => Nat.le_of_not_lt fun hn => ?_, fun h => (range'_sublist_right.2 h).subset⟩
  have ⟨i, h', e⟩ := mem_range'.1 <| h <| mem_range'.2 ⟨_, hn, rfl⟩
  exact Nat.ne_of_gt h' (Nat.eq_of_mul_eq_mul_left step0 (Nat.add_left_cancel e))

theorem range'_subset_right_1 {s m n : Nat} : range' s m ⊆ range' s n ↔ m ≤ n :=
  range'_subset_right (by decide)

theorem get?_range' (s step) : ∀ {m n : Nat}, m < n → get? (range' s n step) m = some (s + step * m)
  | 0, n + 1, _ => rfl
  | m + 1, n + 1, h =>
    (get?_range' (s + step) step (Nat.lt_of_add_lt_add_right h)).trans <| by
      simp [Nat.mul_succ, Nat.add_assoc, Nat.add_comm]

@[simp] theorem get_range' {n m step} (i) (H : i < (range' n m step).length) :
    get (range' n m step) ⟨i, H⟩ = n + step * i :=
  (get?_eq_some.1 <| get?_range' n step (by simpa using H)).2

theorem range'_concat (s n : Nat) : range' s (n + 1) step = range' s n step ++ [s + step * n] := by
  rw [Nat.add_comm n 1]; exact (range'_append s n 1 step).symm

theorem range'_1_concat (s n : Nat) : range' s (n + 1) = range' s n ++ [s + n] := by
  simp [range'_concat]

theorem range_loop_range' : ∀ s n : Nat, range.loop s (range' s n) = range' 0 (n + s)
  | 0, n => rfl
  | s + 1, n => by rw [← Nat.add_assoc, Nat.add_right_comm n s 1]; exact range_loop_range' s (n + 1)

theorem range_eq_range' (n : Nat) : range n = range' 0 n :=
  (range_loop_range' n 0).trans <| by rw [Nat.zero_add]

theorem range_succ_eq_map (n : Nat) : range (n + 1) = 0 :: map succ (range n) := by
  rw [range_eq_range', range_eq_range', range', Nat.add_comm, ← map_add_range']
  congr; exact funext one_add

theorem range'_eq_map_range (s n : Nat) : range' s n = map (s + ·) (range n) := by
  rw [range_eq_range', map_add_range']; rfl

@[simp] theorem length_range (n : Nat) : length (range n) = n := by
  simp only [range_eq_range', length_range']

@[simp] theorem range_eq_nil {n : Nat} : range n = [] ↔ n = 0 := by
  rw [← length_eq_zero, length_range]

theorem range_sublist {m n : Nat} : range m <+ range n ↔ m ≤ n := by
  simp only [range_eq_range', range'_sublist_right]

theorem range_subset {m n : Nat} : range m ⊆ range n ↔ m ≤ n := by
  simp only [range_eq_range', range'_subset_right]

@[simp]
theorem mem_range {m n : Nat} : m ∈ range n ↔ m < n := by
  simp only [range_eq_range', mem_range'_1, Nat.zero_le, true_and, Nat.zero_add]

theorem not_mem_range_self {n : Nat} : n ∉ range n := by simp

theorem self_mem_range_succ (n : Nat) : n ∈ range (n + 1) := by simp

theorem get?_range {m n : Nat} (h : m < n) : get? (range n) m = some m := by
  simp [range_eq_range', get?_range' _ _ h]

theorem range_succ (n : Nat) : range (succ n) = range n ++ [n] := by
  simp only [range_eq_range', range'_1_concat, Nat.zero_add]

@[simp] theorem range_zero : range 0 = [] := rfl

theorem range_add (a b : Nat) : range (a + b) = range a ++ (range b).map (a + ·) := by
  rw [← range'_eq_map_range]
  simpa [range_eq_range', Nat.add_comm] using (range'_append_1 0 a b).symm

theorem iota_eq_reverse_range' : ∀ n : Nat, iota n = reverse (range' 1 n)
  | 0 => rfl
  | n + 1 => by simp [iota, range'_concat, iota_eq_reverse_range' n, reverse_append, Nat.add_comm]

@[simp] theorem length_iota (n : Nat) : length (iota n) = n := by simp [iota_eq_reverse_range']

theorem mem_iota {m n : Nat} : m ∈ iota n ↔ 1 ≤ m ∧ m ≤ n := by
  simp [iota_eq_reverse_range', Nat.add_comm, Nat.lt_succ]

theorem reverse_range' : ∀ s n : Nat, reverse (range' s n) = map (s + n - 1 - ·) (range n)
  | s, 0 => rfl
  | s, n + 1 => by
    rw [range'_1_concat, reverse_append, range_succ_eq_map,
      show s + (n + 1) - 1 = s + n from rfl, map, map_map]
    simp [reverse_range', Nat.sub_right_comm]; rfl

@[simp] theorem get_range {n} (i) (H : i < (range n).length) : get (range n) ⟨i, H⟩ = i :=
  Option.some.inj <| by rw [← get?_eq_get _, get?_range (by simpa using H)]

/-! ### enum, enumFrom -/

@[simp] theorem enumFrom_map_fst (n) :
    ∀ (l : List α), map Prod.fst (enumFrom n l) = range' n l.length
  | [] => rfl
  | _ :: _ => congrArg (cons _) (enumFrom_map_fst _ _)

@[simp] theorem enum_map_fst (l : List α) : map Prod.fst (enum l) = range l.length := by
  simp only [enum, enumFrom_map_fst, range_eq_range']
