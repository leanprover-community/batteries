/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Batteries.Classes.SatisfiesM
public import Std.Tactic.Do

@[expose] public section

/-!
# Results about monadic operations on `List`, in terms of `SatisfiesM`.

-/

namespace List

theorem satisfiesM_foldlM [Monad m] [LawfulMonad m] {f : β → α → m β} (h₀ : motive b)
    (h₁ : ∀ (b) (_ : motive b) (a : α) (_ : a ∈ l), SatisfiesM motive (f b a)) :
    SatisfiesM motive (List.foldlM f b l) := by
  induction l generalizing b with
  | nil => exact SatisfiesM.pure h₀
  | cons hd tl ih =>
    simp only [foldlM_cons]
    apply SatisfiesM.bind_pre
    let ⟨q, qh⟩ := h₁ b h₀ hd mem_cons_self
    exact ⟨(fun ⟨b, bh⟩ => ⟨b, ih bh (fun b bh a am => h₁ b bh a (mem_cons_of_mem hd am))⟩) <$> q,
      by simpa using qh⟩

theorem satisfiesM_foldrM [Monad m] [LawfulMonad m] {f : α → β → m β} (h₀ : motive b)
    (h₁ : ∀ (a : α) (_ : a ∈ l) (b) (_ : motive b), SatisfiesM motive (f a b)) :
    SatisfiesM motive (List.foldrM f b l) := by
  induction l with
  | nil => exact SatisfiesM.pure h₀
  | cons hd tl ih =>
    simp only [foldrM_cons]
    apply SatisfiesM.bind_pre
    let ⟨q, qh⟩ := ih (fun a am b hb => h₁ a (mem_cons_of_mem hd am) b hb)
    exact ⟨(fun ⟨b, bh⟩ => ⟨b, h₁ hd mem_cons_self b bh⟩) <$> q,
      by simpa using qh⟩

end List

namespace Std.Do
set_option mvcgen.warning false
@[spec]
theorem Spec.mapM_list [Monad m] [LawfulMonad m] [WPMonad m ps]
    {xs : List α} {f : α → m β}
    (inv : Invariant xs (List β) ps)
    (step : ∀ pref cur suff (h : xs = pref ++ cur :: suff) acc,
      ⦃inv.1 (⟨pref, cur::suff, h.symm⟩, acc)⦄
        f cur
      ⦃(fun b => inv.1 (⟨pref ++ [cur], suff, by simp [h]⟩, b :: acc), inv.2)⦄) :
    ⦃inv.1 (⟨[], xs, rfl⟩, [])⦄
    xs.mapM f
    ⦃(fun bs => inv.1 (⟨xs, [], by simp⟩, bs.reverse), inv.2)⦄ := by
  rw [List.mapM_eq_reverse_foldlM_cons]
  mvcgen
  invariants
    · inv
  . apply step <;> assumption
  . rw [List.reverse_reverse]

@[spec]
theorem Spec.anyM_list [Monad m] [LawfulMonad m] [WPMonad m ps]
    {xs : List α} {p : α → m Bool}
    {tru : Assertion ps}
    {fal : xs.Cursor → Assertion ps}
    {exc : ExceptConds ps}
    (h0 : ⊢ₛ fal ⟨[], xs, rfl⟩)
    (hp : ∀ pref cur suff (h : xs = pref ++ cur :: suff),
      ⦃fal ⟨pref, cur::suff, h.symm⟩⦄
        p cur
      ⦃(fun b => if b then tru else fal ⟨pref ++ [cur], suff, by simp [h]⟩, exc)⦄) :
    ⦃⌜True⌝⦄
    xs.anyM p
    ⦃(fun res => if res then tru else fal ⟨xs, [], by simp⟩, exc)⦄ := by
  let rec go (pref suff : List α) (hcat : pref ++ suff = xs) :
      ⦃fal ⟨pref, suff, hcat⟩⦄
      suff.anyM p
      ⦃(fun res => if res then tru else fal ⟨xs, [], by simp⟩, exc)⦄ := by
    match suff with
    | [] =>
      rw [List.anyM_nil]
      mvcgen
      simp at hcat
      simp_all
    | y :: ys =>
      rw [List.anyM_cons]
      mvcgen
      mspec hp pref y ys (by simp [hcat])
      split
      · mvcgen
      · mspec (go (pref ++ [y]) ys (by simp [hcat]))
  mvcgen
  mspec go

@[spec]
private theorem Spec.mapFinIdxM_list_go [Monad m] [LawfulMonad m] [WPMonad m ps]
    {xs : List α} {f : (i : Nat) → α → i < xs.length → m β} {exc: ExceptConds ps}
    {motive : Nat → Prop}
    {p : (i : Nat) → β → i < xs.length → Prop}
    (hs : ∀ i (h : i < xs.length), motive i →
      ⦃⌜True⌝⦄ f i xs[i] h ⦃(fun b => ⌜p i b h ∧ motive (i + 1)⌝, exc)⦄)
    {bs : List α} {acc : Array β} {hlen : bs.length + acc.size = xs.length}
    (hsuff : bs = xs.drop acc.size)
    (hmot : motive acc.size)
    (hprev : ∀ i (hi : i < acc.size), p i acc[i] (by omega)) :
    ⦃⌜True⌝⦄
    List.mapFinIdxM.go xs f bs acc hlen
    ⦃(fun result => ⌜motive xs.length ∧
      ∃ eq : result.length = xs.length, ∀ i h, p i result[i] h⌝, exc)⦄ := by
  induction bs generalizing acc with
  | nil =>
    simp [List.mapFinIdxM.go]
    mvcgen
    simp only [List.length_nil, Nat.zero_add] at hlen
    simp_all
  | cons b bs ih =>
    simp only [List.mapFinIdxM.go]
    have hacc : acc.size < xs.length := by simp [List.length_cons] at hlen; omega
    have hb : b = xs[acc.size] := by
      have : (xs.drop acc.size).head? = some b := by rw [← hsuff]; rfl
      simp_all
    subst hb
    mvcgen
    mspec (hs acc.size _ hmot)
    mframe
    rename_i r h
    obtain ⟨h_p, h_motive⟩ := h
    mspec (ih _ (Array.size_push r ▸ h_motive) _)
    . simp only [Array.size_push]
      rw [List.drop_eq_getElem_cons hacc] at hsuff
      exact List.cons_inj_right _ |>.mp ‹_›
    . intro i hi
      simp only [Array.size_push] at hi
      simp only [Array.getElem_push]
      split
      . exact hprev i ‹_›
      . simp_all [show i = acc.size by omega]

@[spec]
theorem Spec.mapFinIdxM_list [Monad m] [LawfulMonad m] [WPMonad m ps]
    {xs : List α} {f : (i : Nat) → α → i < xs.length → m β}
    {motive : Nat → Prop} {exc : ExceptConds ps}
    {p : (i : Nat) → β → i < xs.length → Prop}
    (h0 : motive 0)
    (hs : ∀ i (h : i < xs.length), motive i →
      ⦃⌜True⌝⦄ f i xs[i] h ⦃(fun b => ⌜p i b h ∧ motive (i + 1)⌝, exc)⦄) :
    ⦃⌜True⌝⦄
    xs.mapFinIdxM f
    ⦃(fun bs => ⌜motive xs.length ∧ ∃ eq : bs.length = xs.length, ∀ i h, p i bs[i] h⌝, exc)⦄ := by
  unfold List.mapFinIdxM
  exact Spec.mapFinIdxM_list_go hs (by simp) (by simp [h0]) (fun i hi => absurd hi (by simp))

end Std.Do

namespace List
open Std.Do
set_option mvcgen.warning false

theorem length_mapM {α β : Type u} [Monad m] [LawfulMonad m] [WPMonad m ps]
    {xs : List α} {f : α → m β}
    (hf : ∀ x, ⦃⌜True⌝⦄ f x ⦃⇓ _ => ⌜True⌝⦄) :
    ⦃⌜True⌝⦄
    xs.mapM f
    ⦃⇓ bs => ⌜bs.length = xs.length⌝⦄ := by
  mvcgen invariants
    · ⇓⟨cursor, acc⟩ => ⌜acc.length = cursor.prefix.length⌝
  . mspec hf
    simp_all
  . simp

theorem anyM_iff_exists [Monad m] [LawfulMonad m] [WPMonad m ps]
    {xs : List α} {p : α → m Bool} {q : xs.Cursor → Prop}
    {exc : ExceptConds ps}
    (hp : ∀ pref cur suff (h : xs = pref ++ cur :: suff),
      ⦃⌜True⌝⦄ p cur ⦃(fun b => ⌜b = true ↔ q ⟨pref, cur::suff, h.symm⟩⌝, exc)⦄) :
    ⦃⌜True⌝⦄
    xs.anyM p
    ⦃(fun res => ⌜res = true ↔ ∃ cursor : xs.Cursor, cursor.suffix ≠ [] ∧ q cursor⌝, exc)⦄ := by
  mvcgen
  case vc1.tru =>
    exact ⌜∃ cursor : xs.Cursor, cursor.suffix ≠ [] ∧ q cursor⌝
  case vc2.fal =>
    intro cursor
    exact ⌜∀ c : xs.Cursor, c.suffix ≠ [] → c.prefix.length < cursor.prefix.length → ¬q c⌝
  case vc3.h0 => simp_all
  case vc4.hp pref cur suff h =>
    mspec hp pref cur suff h
    case success prop b =>
      mframe
      rename_i hiff
      split <;> mpure_intro
      case isTrue => exact ⟨⟨pref, cur :: suff, h.symm⟩, (by simp), hiff.mp ‹_›⟩
      intro c hsuff hlen
      simp only [List.length_append, List.length_singleton] at hlen
      by_cases hc : c.prefix.length < pref.length
      case pos => simp_all
      have hceq := List.append_inj (c.property.trans h) (by omega)
      simp_all [show ⟨pref, cur :: suff, h.symm⟩ = c by cases c; simp_all]
  case vc5.success r =>
    split
    case isTrue => simp_all
    rename_i hr
    mframe
    mpure_intro
    rename_i hfal
    simp only [hr, Bool.false_eq_true, false_iff, not_exists, not_and]
    intro c hsuff hq
    simp only [← c.property, List.length_append] at hfal
    simp_all [List.length_pos_iff]

end List
