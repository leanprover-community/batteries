/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Std.Data.List.Count

/-!
# Pairwise relations on a list

This file provides basic results about `List.Pairwise` and `List.pwFilter` (definitions are in
`Data.List.Defs`).
`Pairwise r [a 0, ..., a (n - 1)]` means `∀ i j, i < j → r (a i) (a j)`. For example,
`Pairwise (≠) l` means that all elements of `l` are distinct, and `Pairwise (<) l` means that `l`
is strictly increasing.
`pwFilter r l` is the list obtained by iteratively adding each element of `l` that doesn't break
the pairwiseness of the list we have so far. It thus yields `l'` a maximal sublist of `l` such that
`Pairwise r l'`.

## Tags

sorted, nodup
-/


open Nat Function

namespace List

variable {α β : Type _} {R S T : α → α → Prop} {a : α} {l : List α}


/-! ### Pairwise -/

theorem rel_of_pairwise_cons (p : (a :: l).Pairwise R) : ∀ {a'}, a' ∈ l → R a a' :=
  (pairwise_cons.1 p).1 _

theorem Pairwise.of_cons (p : (a :: l).Pairwise R) : Pairwise R l :=
  (pairwise_cons.1 p).2

theorem Pairwise.tail : ∀ {l : List α} (_p : Pairwise R l), Pairwise R l.tail
  | [], h => h
  | _ :: _, h => h.of_cons

theorem Pairwise.drop : ∀ {l : List α} {n : Nat}, List.Pairwise R l → List.Pairwise R (l.drop n)
  | _, 0, h => h
  | [], _ + 1, _ => List.Pairwise.nil
  | a :: l, n + 1, h => by rw [List.drop]; exact Pairwise.drop (pairwise_cons.mp h).right

theorem Pairwise.imp_of_mem {S : α → α → Prop} {l : List α}
    (H : ∀ {a b}, a ∈ l → b ∈ l → R a b → S a b) (p : Pairwise R l) : Pairwise S l := by
  induction p with
  | nil => constructor
  | @cons a l r _ ih =>
    constructor
    · exact fun x h => H (mem_cons_self _ _) (mem_cons_of_mem _ h) <| r x h
    · exact ih fun {a b} m m' => H (mem_cons_of_mem _ m) (mem_cons_of_mem _ m')

theorem pairwise_and_iff : (l.Pairwise fun a b => R a b ∧ S a b) ↔ l.Pairwise R ∧ l.Pairwise S :=
  ⟨ fun h => ⟨h.imp @fun a b h => h.1, h.imp @fun a b h => h.2⟩
  , fun ⟨hR, hS⟩ => by
    induction hR with
    | nil => simp only [Pairwise.nil]
    | cons R1 R2 IH =>
      simp only [Pairwise.nil, pairwise_cons] at hS ⊢
      exact ⟨fun b bl => ⟨R1 b bl, hS.1 b bl⟩, IH ⟨R2, hS.2⟩ hS.2⟩⟩

theorem Pairwise.and (hR : l.Pairwise R) (hS : l.Pairwise S) :
    l.Pairwise fun a b => R a b ∧ S a b :=
  pairwise_and_iff.2 ⟨hR, hS⟩

theorem Pairwise.imp₂ (H : ∀ a b, R a b → S a b → T a b) (hR : l.Pairwise R) (hS : l.Pairwise S) :
    l.Pairwise T :=
  (hR.and hS).imp fun h => (H _ _ h.1 h.2)

theorem Pairwise.iff_of_mem {S : α → α → Prop} {l : List α}
    (H : ∀ {a b}, a ∈ l → b ∈ l → (R a b ↔ S a b)) : Pairwise R l ↔ Pairwise S l :=
  ⟨Pairwise.imp_of_mem fun {_ _} m m' => (H m m').1,
   Pairwise.imp_of_mem fun {_ _} m m' => (H m m').2⟩

theorem Pairwise.iff {S : α → α → Prop} (H : ∀ a b, R a b ↔ S a b) {l : List α} :
    Pairwise R l ↔ Pairwise S l :=
  Pairwise.iff_of_mem fun _ _ => H _ _

theorem pairwise_of_forall {l : List α} (H : ∀ x y, R x y) : Pairwise R l := by
  induction l
  · exact Pairwise.nil
  · simp only [*, pairwise_cons, and_true]; intros; trivial

theorem Pairwise.and_mem {l : List α} :
    Pairwise R l ↔ Pairwise (fun x y => x ∈ l ∧ y ∈ l ∧ R x y) l :=
  Pairwise.iff_of_mem
    (by simp (config := { contextual := true }) only [true_and, iff_self]; intros; trivial)

theorem Pairwise.imp_mem {l : List α} :
    Pairwise R l ↔ Pairwise (fun x y => x ∈ l → y ∈ l → R x y) l :=
  Pairwise.iff_of_mem
    (by simp (config := { contextual := true }) only [forall_prop_of_true, iff_self]
        intros; trivial)

theorem Pairwise.forall_of_forall_of_flip (h₁ : ∀ x ∈ l, R x x) (h₂ : l.Pairwise R)
    (h₃ : l.Pairwise (flip R)) : ∀ ⦃x⦄, x ∈ l → ∀ ⦃y⦄, y ∈ l → R x y := by
  induction l with
  | nil => exact forall_mem_nil _
  | cons a l ih =>
    rw [pairwise_cons] at h₂ h₃
    simp only [mem_cons]
    rintro x (rfl | hx) y (rfl | hy)
    · exact h₁ _ (l.mem_cons_self _)
    · exact h₂.1 _ hy
    · exact h₃.1 _ hx
    · exact ih (fun x hx => h₁ _ <| mem_cons_of_mem _ hx) h₂.2 h₃.2 hx hy

theorem pairwise_singleton (R) (a : α) : Pairwise R [a] := by
  simp only [pairwise_cons, not_mem_nil, false_implies,
    implies_true, Pairwise.nil, and_self]

theorem pairwise_pair {a b : α} : Pairwise R [a, b] ↔ R a b := by
  simp only [pairwise_cons, mem_singleton, forall_eq, Pairwise.nil,
    and_true, not_mem_nil, false_implies, implies_true]

theorem pairwise_append_comm (s : ∀ {x y}, R x y → R y x) {l₁ l₂ : List α} :
    Pairwise R (l₁ ++ l₂) ↔ Pairwise R (l₂ ++ l₁) := by
  have : ∀ l₁ l₂ : List α, (∀ x : α, x ∈ l₁ → ∀ y : α, y ∈ l₂ → R x y) →
    ∀ x : α, x ∈ l₂ → ∀ y : α, y ∈ l₁ → R x y := fun l₁ l₂ a x xm y ym => s (a y ym x xm)
  simp only [pairwise_append, and_left_comm]; rw [Iff.intro (this l₁ l₂) (this l₂ l₁)]

theorem pairwise_middle (s : ∀ {x y}, R x y → R y x) {a : α} {l₁ l₂ : List α} :
    Pairwise R (l₁ ++ a :: l₂) ↔ Pairwise R (a :: (l₁ ++ l₂)) :=
  show Pairwise R (l₁ ++ ([a] ++ l₂)) ↔ Pairwise R ([a] ++ l₁ ++ l₂) by
    rw [← append_assoc, pairwise_append, @pairwise_append _ _ ([a] ++ l₁), pairwise_append_comm s]
    simp only [mem_append, or_comm]

theorem Pairwise.of_map {S : β → β → Prop} (f : α → β) (H : ∀ a b : α, S (f a) (f b) → R a b)
    (p : Pairwise S (map f l)) : Pairwise R l :=
  (pairwise_map.1 p).imp (H _ _)

theorem Pairwise.map {S : β → β → Prop} (f : α → β) (H : ∀ a b : α, R a b → S (f a) (f b))
    (p : Pairwise R l) : Pairwise S (map f l) :=
  pairwise_map.2 <| p.imp (H _ _)

theorem pairwise_filterMap (f : β → Option α) {l : List β} :
    Pairwise R (filterMap f l) ↔ Pairwise (fun a a' : β => ∀ b ∈ f a, ∀ b' ∈ f a', R b b') l := by
  let _S (a a' : β) := ∀ b ∈ f a, ∀ b' ∈ f a', R b b'
  simp only [Option.mem_def]
  induction l with
  | nil => simp only [filterMap, Pairwise.nil]
  | cons a l IH =>
  match e : f a with
  | none =>
    rw [filterMap_cons_none _ _ e, pairwise_cons]
    simp only [e, false_implies, implies_true, true_and, IH]
  | some b =>
    rw [filterMap_cons_some _ _ _ e]
    simp [IH, e]
    intro _
    exact ⟨fun h a ha b hab => h _ _ ha hab, fun h a b ha hab => h _ ha _ hab⟩

theorem Pairwise.filter_map {S : β → β → Prop} (f : α → Option β)
    (H : ∀ a a' : α, R a a' → ∀ b ∈ f a, ∀ b' ∈ f a', S b b') {l : List α} (p : Pairwise R l) :
    Pairwise S (filterMap f l) :=
  (pairwise_filterMap _).2 <| p.imp (H _ _)

theorem pairwise_filter (p : α → Prop) [DecidablePred p] {l : List α} :
    Pairwise R (filter p l) ↔ Pairwise (fun x y => p x → p y → R x y) l := by
  rw [← filterMap_eq_filter, pairwise_filterMap]
  apply Pairwise.iff; intros
  simp only [decide_eq_true_eq, Option.mem_def, Option.guard_eq_some, and_imp, forall_eq']

theorem Pairwise.filter (p : α → Bool) : Pairwise R l → Pairwise R (filter p l) :=
  Pairwise.sublist (filter_sublist _)

theorem pairwise_join {L : List (List α)} :
    Pairwise R (join L) ↔
      (∀ l ∈ L, Pairwise R l) ∧ Pairwise (fun l₁ l₂ => ∀ x ∈ l₁, ∀ y ∈ l₂, R x y) L := by
  induction L with
  | nil =>
    simp only [join, Pairwise.nil, not_mem_nil, false_implies,
      forall_const, and_self]
  | cons l L IH =>
    simp only [join, pairwise_append, IH, mem_join, exists_imp, and_imp, forall_mem_cons,
      pairwise_cons, and_assoc, and_congr_right_iff]
    rw [and_comm, and_congr_left_iff]
    intros
    exact ⟨fun h a b c d e => h c d e a b, fun h c d e a b => h a b c d e⟩

@[reducible]
def Function.swap {φ : α → β → Sort u₃} (f : ∀ x y, φ x y) : ∀ y x, φ x y :=
  λ y x => f x y

theorem forall_swap {p : α → β → Prop} : (∀ x y, p x y) ↔ ∀ y x, p x y :=
  ⟨Function.swap, Function.swap⟩

theorem forall_imp_swap {p : α → Prop} : (∀ x, H → p x) ↔ (H → ∀ x, p x) :=
  ⟨λ x y z => x z y, λ x y z => x z y⟩

theorem pairwise_bind {R : β → β → Prop} {l : List α} {f : α → List β} :
    List.Pairwise R (l.bind f) ↔
      (∀ a ∈ l, Pairwise R (f a)) ∧ Pairwise (fun a₁ a₂ => ∀ x ∈ f a₁, ∀ y ∈ f a₂, R x y) l :=
  by simp [List.bind, pairwise_join, pairwise_map, mem_map,
      forall_swap (α := List β), forall_imp_swap (α := List β)]

theorem pairwise_of_reflexive_on_dupl_of_forall_ne [DecidableEq α] {l : List α} {r : α → α → Prop}
    (hr : ∀ a, 1 < count a l → r a a) (h : ∀ a ∈ l, ∀ b ∈ l, a ≠ b → r a b) : l.Pairwise r := by
  induction l with
  | nil => simp
  | cons hd tl IH =>
    rw [List.pairwise_cons]
    constructor
    · intro x hx
      by_cases H : hd = x
      · rw [H]
        refine' hr _ _
        simp [H, Nat.add_one]
        apply Nat.succ_le_succ
        simp [hx]
      · exact h hd (mem_cons_self _ _) x (mem_cons_of_mem _ hx) H
    · refine' IH _ _
      · intro x hx
        refine' hr _ _
        rw [count_cons]
        split
        · exact Nat.lt_trans hx (Nat.lt_succ_self _)
        · exact hx
      · intro x hx y hy
        exact h x (mem_cons_of_mem _ hx) y (mem_cons_of_mem _ hy)

theorem pairwise_iff_get : ∀ {l : List α}, Pairwise R l ↔
    ∀ (i j) (_hij : i < j), R (get l i) (get l j)
  | [] => by
    simp only [Pairwise.nil, true_iff]; exact fun i j _h => (Nat.not_lt_zero j).elim j.2
  | a :: l => by
    rw [pairwise_cons, pairwise_iff_get]
    refine'
      ⟨fun H i j hij => _, fun H =>
        ⟨fun a' m => _, fun i j hij => _⟩⟩
    · let ⟨j,hj⟩ := j
      match j with
      | zero => exact (Nat.not_lt_zero _).elim hij
      | succ j =>
      let ⟨i,hi⟩ := i
      match i with
      | zero    => exact H.1 _ (get_mem l _ _)
      | succ _  => exact H.2 _ _ (Nat.lt_of_succ_lt_succ hij)
    · rcases get_of_mem m with ⟨n, h, rfl⟩
      have := H ⟨0, show 0 < (a::l).length from Nat.succ_pos _⟩ ⟨n.succ, Nat.succ_lt_succ n.2⟩
        (Nat.succ_pos n)
      simp at this
      exact this
    . have := H i.succ j.succ (show i.1.succ < j.1.succ from Nat.succ_lt_succ hij)
      simp at this
      exact this

theorem pairwise_replicate {α : Type _} {r : α → α → Prop} {x : α} (hx : r x x) :
    ∀ n : Nat, Pairwise r (List.replicate n x)
  | 0 => by simp
  | n + 1 => by
    simp only [ replicate, add_eq, Nat.add_zero, pairwise_cons, mem_replicate, ne_eq,
                and_imp, hx, and_true, pairwise_replicate hx n ]
    intro _ _ h
    cases h; assumption

/-! ### Pairwise filtering -/

variable [DecidableRel R]

@[simp]
theorem pwFilter_nil : pwFilter R [] = [] :=
  rfl

@[simp]
theorem pwFilter_cons_of_pos {a : α} {l : List α} (h : ∀ b ∈ pwFilter R l, R a b) :
    pwFilter R (a :: l) = a :: pwFilter R l :=
  if_pos h

@[simp]
theorem pwFilter_cons_of_neg {a : α} {l : List α} (h : ¬∀ b ∈ pwFilter R l, R a b) :
    pwFilter R (a :: l) = pwFilter R l :=
  if_neg h

theorem pwFilter_map (f : β → α) :
    ∀ l : List β, pwFilter R (map f l) = map f (pwFilter (fun x y => R (f x) (f y)) l)
  | [] => rfl
  | x :: xs =>
    if h : ∀ b ∈ pwFilter R (map f xs), R (f x) b then
      by
      have h' : ∀ b : β, b ∈ pwFilter (fun x y : β => R (f x) (f y)) xs → R (f x) (f b) :=
        fun b hb => h _ (by rw [pwFilter_map f xs]; apply mem_map_of_mem _ hb)
      rw [map, pwFilter_cons_of_pos h, pwFilter_cons_of_pos h', pwFilter_map f xs, map]
    else
      by
      have h' : ¬∀ b : β, b ∈ pwFilter (fun x y : β => R (f x) (f y)) xs → R (f x) (f b) :=
        fun hh =>
        h fun a ha => by
          rw [pwFilter_map f xs, mem_map] at ha
          rcases ha with ⟨b, hb₀, hb₁⟩
          subst a
          exact hh _ hb₀
      rw [map, pwFilter_cons_of_neg h, pwFilter_cons_of_neg h', pwFilter_map f xs]

theorem pwFilter_sublist : ∀ l : List α, pwFilter R l <+ l
  | [] => nil_sublist _
  | x :: l => by
    by_cases h : ∀ y ∈ pwFilter R l, R x y
    · rw [pwFilter_cons_of_pos h]
      exact (pwFilter_sublist l).cons₂ _
    · rw [pwFilter_cons_of_neg h]
      exact Sublist.cons _ (pwFilter_sublist l)

theorem pwFilter_subset (l : List α) : pwFilter R l ⊆ l :=
  (pwFilter_sublist _).subset

theorem pairwise_pwFilter : ∀ l : List α, Pairwise R (pwFilter R l)
  | [] => Pairwise.nil
  | x :: l => by
    by_cases h : ∀ y ∈ pwFilter R l, R x y
    · rw [pwFilter_cons_of_pos h]
      exact pairwise_cons.2 ⟨h, pairwise_pwFilter l⟩
    · rw [pwFilter_cons_of_neg h]
      exact pairwise_pwFilter l

theorem pwFilter_eq_self {l : List α} : pwFilter R l = l ↔ Pairwise R l :=
  ⟨fun e => e ▸ pairwise_pwFilter l, fun p =>
    by
    induction l with
    | nil => rfl
    | cons x l IH =>
      let ⟨al, p⟩ := pairwise_cons.1 p
      have : pwFilter R (x :: l) = _ := pwFilter_cons_of_pos (by
        intro b hb
        rw [IH p] at hb
        apply al _ hb)
      rw [this, IH p]⟩

@[simp]
theorem pwFilter_idempotent : pwFilter R (pwFilter R l) = pwFilter R l := by
  rw [pwFilter_eq_self]
  apply pairwise_pwFilter

section variable {p q r : α → Prop} {P Q : ∀ x, p x → Prop}
theorem BAll.imp_right (H : ∀ x h, P x h → Q x h) (h₁ : ∀ x h, P x h) (x h) : Q x h :=
  H _ _ <| h₁ _ _
theorem BAll.imp_left (H : ∀ x, p x → q x) (h₁ : ∀ x, q x → r x) (x) (h : p x) : r x :=
  h₁ _ <| H _ h
end

theorem forall_mem_pwFilter (neg_trans : ∀ {x y z}, R x z → R x y ∨ R y z) (a : α) (l : List α) :
    (∀ b ∈ pwFilter R l, R a b) ↔ ∀ b ∈ l, R a b :=
  ⟨by
    induction l with
    | nil => exact fun _ _ h => (not_mem_nil _ h).elim
    | cons x l IH =>
      simp only [forall_mem_cons]
      by_cases h : ∀ y ∈ pwFilter R l, R x y <;> dsimp at h
      · simp only [pwFilter_cons_of_pos h, forall_mem_cons, and_imp]
        exact fun r H => ⟨r, IH H⟩
      · rw [pwFilter_cons_of_neg h]
        refine fun H => ⟨?_, IH H⟩
        match e : find? (fun y => ¬R x y) (pwFilter R l) with
        | none =>
          refine h.elim (fun y hy => ?_)
          have := find?_eq_none.1 e y hy
          revert this
          simp only [decide_not, Bool.not_eq_true, Bool.not_eq_false', decide_eq_true_iff, imp_self]
        | some k =>
          have := find?_some e
          apply (neg_trans (H k (mem_of_find?_eq_some e))).resolve_right
          rw [decide_eq_true_iff] at this; exact this
    , by
      intro h b hb
      apply h; apply pwFilter_subset (R := R)
      exact hb⟩
