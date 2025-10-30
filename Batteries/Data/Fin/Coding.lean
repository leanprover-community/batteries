/-
Copyright (c) 2024 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: François G. Dorais
-/
module

public import Batteries.Data.Char
public import Batteries.Data.Fin.Lemmas
public import Batteries.Tactic.Basic
public import Batteries.Tactic.Trans
public import Batteries.Tactic.Lint

@[expose] public section

/-! # Low-level coding recipes for `Fin` types

This module collects encoding/decoding bijections to represent basic type constructors of `Fin`
types as `Fin` types. These functions implement the isomorphism `Option (Fin n) ≃ Fin (n+1)`,
`Fin m ⊕ Fin n ≃ Fin (m + n)`, `Fin m × Fin n ≃ Fin (m * n)`, ..., including, dependent sums,
dependent products, decidable subtypes and decidable quotients.

Only a minimal API is provided. These utility functions are intended for use in other constructions.
Such constructions should avoid exposing these functions as they are not meant for public use.
-/

namespace Fin

/-- Encode `Empty` into `Fin 0`. -/
def encodeEmpty : Empty → Fin 0 := (nomatch ·)

/-- Decode `Empty` from `Fin 0`. -/
def decodeEmpty : Fin 0 → Empty := (nomatch ·)

@[simp] theorem encodeEmpty_decodeEmpty (x : Fin 0) : encodeEmpty (decodeEmpty x) = x := nomatch x

@[simp] theorem decodeEmpty_encodeEmpty (x : Empty) : decodeEmpty (encodeEmpty x) = x := nomatch x

/-- Encode `PUnit` into `Fin 1`. -/
@[nolint unusedArguments]
def encodePUnit : PUnit → Fin 1
  | .unit => 0

/-- Decode `PUnit` from `Fin 1`. -/
@[pp_nodot] def decodePUnit : Fin 1 → PUnit
  | 0 => .unit

/-- Encode `Unit` into `Fin 1`. -/
abbrev encodeUnit : Unit → Fin 1 := encodePUnit

/-- Decode `Unit` from `Fin 1`. -/
@[pp_nodot] abbrev decodeUnit : Fin 1 → Unit := decodePUnit

@[simp] theorem encodePUnit_decodePUnit : (x : Fin 1) → encodePUnit (decodePUnit x) = x
  | 0 => rfl

@[simp] theorem decodePUnit_encodePUnit : (x : PUnit) → decodePUnit (encodePUnit x) = x
  | .unit => rfl

/-- Encode `Bool` into `Fin 2`. -/
def encodeBool : Bool → Fin 2
  | false => 0
  | true => 1

/-- Decode `Bool` from `Fin 2`. -/
@[pp_nodot] def decodeBool : Fin 2 → Bool
  | 0 => false
  | 1 => true

@[simp] theorem encodeBool_decodeBool : (x : Fin 2) → encodeBool (decodeBool x) = x
  | 0 | 1 => rfl

@[simp] theorem decodeBool_encodeBool : (x : Bool) → decodeBool (encodeBool x) = x
  | false | true => rfl

/-- Encode `Ordering` into `Fin 3`. -/
def encodeOrdering : Ordering → Fin 3
  | .eq => 0
  | .lt => 1
  | .gt => 2

/-- Decode `Ordering` from `Fin 3`. -/
@[pp_nodot] def decodeOrdering : Fin 3 → Ordering
  | 0 => .eq
  | 1 => .lt
  | 2 => .gt

@[simp] theorem encodeOrdering_decodeOrdering : (x : Fin 3) → encodeOrdering (decodeOrdering x) = x
  | 0 | 1 | 2 => rfl

@[simp] theorem decodeOrdering_encodeOrdering :
    (x : Ordering) → decodeOrdering (encodeOrdering x) = x
  | .eq | .lt | .gt => rfl

/-- Encode `Char` into `Fin Char.count`. -/
def encodeChar (c : Char) : Fin Char.count :=
  if _ : c.toNat < Char.minSurrogate then
    ⟨c.toNat, by grind⟩
  else
    ⟨c.toNat - (Char.maxSurrogate + 1 - Char.minSurrogate), by cases c; grind [Char.toNat]⟩

/-- Decode `Char` from `Fin Char.count`. -/
@[pp_nodot] def decodeChar (i : Fin Char.count) : Char :=
  if _ : i.val < 0xD800 then
    Char.ofNatAux i.val (by grind)
  else
    Char.ofNatAux (i.val + (Char.maxSurrogate + 1 - Char.minSurrogate)) (by grind)

@[simp] theorem encodeChar_decodeChar (x) : encodeChar (decodeChar x) = x := by
  simp only [decodeChar, encodeChar]
  split
  · simp [*]
  · have : ¬ x.val + (Char.maxSurrogate + 1 - Char.minSurrogate) < Char.minSurrogate := by grind
    simp [*]

@[simp] theorem decodeChar_encodeChar (x) : decodeChar (encodeChar x) = x := by
  ext; simp only [decodeChar, encodeChar]
  split
  · simp only [Char.ofNatAux, Char.toNat]; rfl
  · have : ¬ x.toNat - (Char.maxSurrogate + 1 - Char.minSurrogate) < Char.minSurrogate := by
      cases x; grind [Char.toNat]
    have : Char.maxSurrogate + 1 - Char.minSurrogate ≤ x.toNat := by grind
    simp [Char.ofNatAux, *]; rfl

/-- Encode `Option (Fin n)` into `Fin (n+1)`. -/
def encodeOption : Option (Fin n) → Fin (n+1)
  | none => 0
  | some ⟨i, h⟩ => ⟨i+1, Nat.succ_lt_succ h⟩

/-- Decode `Option (Fin n)` from `Fin (n+1)`. -/
@[pp_nodot] def decodeOption : Fin (n+1) → Option (Fin n)
  | 0 => none
  | ⟨i+1, h⟩ => some ⟨i, Nat.lt_of_succ_lt_succ h⟩

@[simp] theorem encodeOption_decodeOption (x : Fin (n+1)) : encodeOption (decodeOption x) = x := by
  simp only [encodeOption, decodeOption]
  split
  · next hd =>
    split at hd
    · next he => cases he; rfl
    · contradiction
  · next hd =>
    split at hd
    · contradiction
    · next he => cases hd; simp

@[simp] theorem decodeOption_encodeOption (x : Option (Fin n)) :
    decodeOption (encodeOption x) = x := by
  simp only [encodeOption, decodeOption]
  split
  · next he =>
    split at he
    · rfl
    · cases he
  · next he =>
    split at he
    · cases he
    · cases he; rfl

/-- Encode `Fin n ⊕ Fin m` into `Fin (n + m)`. -/
def encodeSum : Sum (Fin n) (Fin m) → Fin (n + m)
  | .inl x => x.castAdd _
  | .inr x => x.natAdd _

/-- Decode `Fin n ⊕ Fin m` from `Fin (n + m)`. -/
@[pp_nodot] def decodeSum (x : Fin (n + m)) : Sum (Fin n) (Fin m) :=
  x.addCases .inl .inr

@[simp] theorem encodeSum_decodeSum (x : Fin (n + m)) :
    encodeSum (decodeSum x) = x := by
  simp only [encodeSum, decodeSum]
  cases x using addCases <;> simp

@[simp] theorem decodeSum_encodeSum (x : Sum (Fin n) (Fin m)) :
    decodeSum (encodeSum x) = x := by
  simp only [encodeSum, decodeSum]
  cases x <;> simp

/-- Encode `Fin m × Fin n` into `Fin (m * n)`. -/
def encodeProd : Fin m × Fin n → Fin (m * n)
  | (i, j) => mkDivMod i j

/-- Decode `Fin m × Fin n` from `Fin (m * n)`. -/
@[pp_nodot] def decodeProd (z : Fin (m * n)) : Fin m × Fin n :=
  (z.divNat, z.modNat)

@[simp] theorem encodeProd_decodeProd (x : Fin (m * n)) : encodeProd (decodeProd x) = x := by
  simp [encodeProd, decodeProd]

@[simp] theorem decodeProd_encodeProd (x : Fin m × Fin n) : decodeProd (encodeProd x) = x := by
  simp [encodeProd, decodeProd]

/-- Encode `(i : Fin n) × Fin (f i)` into `Fin (Fin.sum f)`. -/
def encodeSigma (f : Fin n → Nat) (x : (i : Fin n) × Fin (f i)) : Fin (Fin.sum f) :=
  match n, f, x with
  | _+1, f, ⟨0, j⟩ =>
    ⟨j, Nat.lt_of_lt_of_le j.is_lt (sum_succ f .. ▸ Nat.le_add_right ..)⟩
  | _+1, f, ⟨⟨i+1, hi⟩, j⟩ =>
    match encodeSigma ((f ·.succ)) ⟨⟨i, Nat.lt_of_succ_lt_succ hi⟩, j⟩ with
    | ⟨k, hk⟩ => ⟨f 0 + k, sum_succ f .. ▸ Nat.add_lt_add_left hk ..⟩

/-- Decode `(i : Fin n) × Fin (f i)` from `Fin (Fin.sum f)`. -/
@[pp_nodot] def decodeSigma (f : Fin n → Nat) (x : Fin (Fin.sum f)) : (i : Fin n) × Fin (f i) :=
  match n, f, x with
  | 0, _, ⟨_, h⟩ => False.elim (by simp at h)
  | n+1, f, ⟨x, hx⟩ =>
    if hx0 : x < f 0 then
      ⟨0, ⟨x, hx0⟩⟩
    else
      have hxf : x - f 0 < Fin.sum (f ·.succ) := by grind [sum_succ]
      match decodeSigma ((f ·.succ)) ⟨x - f 0, hxf⟩ with
      | ⟨⟨i, hi⟩, y⟩ => ⟨⟨i+1, Nat.succ_lt_succ hi⟩, y⟩

@[simp] theorem encodeSigma_decodeSigma (f : Fin n → Nat) (x : Fin (Fin.sum f)) :
    encodeSigma f (decodeSigma f x) = x := by
  induction n with
  | zero => absurd x.is_lt; simp
  | succ n ih =>
    simp only [decodeSigma]
    split
    · rfl
    · next h1 =>
      have h2 : x - f 0 < Fin.sum (f ·.succ) := by grind [sum_succ]
      have : encodeSigma (f ·.succ) (decodeSigma (f ·.succ) ⟨x - f 0, h2⟩) = ↑x - f 0 := by
        rw [ih]
      ext; simp only [encodeSigma]
      conv => rhs; rw [← Nat.add_sub_of_le (Nat.le_of_not_gt h1)]
      congr

@[simp] theorem decodeSigma_encodeSigma (f : Fin n → Nat) (x : (i : Fin n) × Fin (f i)) :
    decodeSigma f (encodeSigma f x) = x := by
  induction n with
  | zero => nomatch x
  | succ n ih =>
    simp only [decodeSigma]
    match x with
    | ⟨⟨0, _⟩, x, hx⟩ =>
      split
      · rfl
      · grind [encodeSigma]
    | ⟨⟨i+1, hi⟩, ⟨x, hx⟩⟩ =>
      have : ¬ encodeSigma f ⟨⟨i+1, hi⟩, ⟨x, hx⟩⟩ < f 0 := by simp [encodeSigma]
      rw [dif_neg this]
      have : (encodeSigma f ⟨⟨i+1, hi⟩, ⟨x, hx⟩⟩).1 - f 0 =
          (encodeSigma (f ·.succ) ⟨⟨i, Nat.lt_of_succ_lt_succ hi⟩, ⟨x, hx⟩⟩).1 := by
        simp [encodeSigma, Nat.add_sub_cancel_left]
      have h := ih (f ·.succ) ⟨⟨i, Nat.lt_of_succ_lt_succ hi⟩, ⟨x, hx⟩⟩
      simp [Sigma.ext_iff, Fin.ext_iff] at h ⊢
      constructor
      · conv => rhs; rw [← h.1]
        apply congrArg
        apply congrArg Sigma.fst
        congr
      · apply HEq.trans _ h.2; congr

/-- Encode `Fin m → Fin n` into `Fin (n ^ m)`. -/
def encodeFun : {m : Nat} → (Fin m → Fin n) → Fin (n ^ m)
  | 0, _ => ⟨0, by simp⟩
  | m+1, f => Fin.mk (n * (encodeFun fun k => f k.succ).val + (f 0).val) <| calc
    _ < n * (encodeFun fun k => f k.succ).val + n := Nat.add_lt_add_left (f 0).isLt _
    _ = n * ((encodeFun fun k => f k.succ).val + 1) := Nat.mul_succ ..
    _ ≤ n * n ^ m := Nat.mul_le_mul_left n (Nat.succ_le_of_lt (encodeFun fun k => f k.succ).isLt)
    _ = n ^ m * n := Nat.mul_comm ..
    _ = n ^ (m+1) := Nat.pow_succ ..

/-- Decode `Fin m → Fin n` from `Fin (n ^ m)`. -/
@[pp_nodot] def decodeFun : {m : Nat} → Fin (n ^ m) → Fin m → Fin n
  | 0, _ => (nomatch .)
  | m+1, ⟨k, hk⟩ =>
    have hn : n > 0 := by grind
    fun
    | 0 => ⟨k % n, Nat.mod_lt k hn⟩
    | ⟨i+1, hi⟩ =>
      have h : k / n < n ^ m := by rw [Nat.div_lt_iff_lt_mul hn]; exact hk
      decodeFun ⟨k / n, h⟩ ⟨i, Nat.lt_of_succ_lt_succ hi⟩

@[simp] theorem encodeFun_decodeFun (x : Fin (n ^ m)) : encodeFun (decodeFun x) = x := by
  induction m with simp only [encodeFun, decodeFun, Fin.succ]
  | zero => grind
  | succ m ih => cases x; simp [ih]; rw [← Fin.zero_eta, Nat.div_add_mod]

@[simp] theorem decodeFun_encodeFun (x : Fin m → Fin n) : decodeFun (encodeFun x) = x := by
  funext i; induction m with simp only [encodeFun, decodeFun]
  | zero => nomatch i
  | succ m ih =>
    have hn : 0 < n := Nat.zero_lt_of_lt (x 0).is_lt
    split
    · ext; simp [Nat.mod_eq_of_lt]
    · next i hi =>
      have : decodeFun (encodeFun fun k => x k.succ) ⟨i, Nat.lt_of_succ_lt_succ hi⟩
          = x ⟨i+1, hi⟩ := by rw [ih]; rfl
      simp [← this, Nat.mul_add_div hn, Nat.div_eq_of_lt]

/-- Encode `(i : Fin n) → Fin (f i)` into `Fin (Fin.prod f)`. -/
def encodePi (f : Fin n → Nat) (x : (i : Fin n) → Fin (f i)) : Fin (Fin.prod f) :=
  match n, f, x with
  | 0, _, _ => ⟨0, by simp [Fin.prod]⟩
  | _+1, f, x =>
    match encodePi ((f ·.succ)) (fun ⟨i, hi⟩ => x ⟨i+1, Nat.succ_lt_succ hi⟩) with
    | ⟨k, hk⟩ => Fin.mk (f 0 * k + (x 0).val) $ calc
      _ < f 0 * k + f 0 := by grind
      _ = f 0 * (k + 1) := by grind
      _ ≤ f 0 * Fin.prod (f ∘ succ) := Nat.mul_le_mul_left _ (Nat.succ_le_of_lt hk)
      _ = Fin.prod f := Eq.symm <| prod_succ ..

/-- Decode `(i : Fin n) → Fin (f i)` from `Fin (Fin.prod f)`. -/
def decodePi (f : Fin n → Nat) (x : Fin (Fin.prod f)) : (i : Fin n) → Fin (f i) :=
  match n, f, x with
  | 0, _, _ => (nomatch ·)
  | n+1, f, ⟨x, hx⟩ =>
    have h : f 0 > 0 := by grind [prod_succ]
    have : x / f 0 < Fin.prod (f ·.succ) := by
      rw [Nat.div_lt_iff_lt_mul h, Nat.mul_comm, ← prod_succ]
      exact hx
    match decodePi ((f ·.succ)) ⟨x / f 0, this⟩ with
    | t => fun
      | ⟨0, _⟩ => ⟨x % f 0, Nat.mod_lt x h⟩
      | ⟨i+1, hi⟩ => t ⟨i, Nat.lt_of_succ_lt_succ hi⟩

@[simp] theorem encodePi_decodePi (f : Fin n → Nat) (x : Fin (Fin.prod f)) :
    encodePi f (decodePi f x) = x := by
  induction n with
  | zero =>
    match x with
    | ⟨0, _⟩ => rfl
    | ⟨_+1, h⟩ => simp at h
  | succ n ih =>
    simp only [encodePi, decodePi, ih]
    ext
    conv => rhs; rw [← Nat.div_add_mod x (f 0)]
    congr

@[simp] theorem decodePi_encodePi (f : Fin n → Nat) (x : (i : Fin n) → Fin (f i)) :
    decodePi f (encodePi f x) = x := by
  induction n with
  | zero => funext i; nomatch i
  | succ n ih =>
    have h0 : 0 < f 0 := Nat.zero_lt_of_lt (x 0).is_lt
    funext i
    simp only [decodePi]
    split
    · simp [encodePi, Nat.mod_eq_of_lt (x 0).is_lt]
    · next i hi =>
      have h : decodePi (f ·.succ) (encodePi (f ·.succ) fun i => x i.succ)
          ⟨i, Nat.lt_of_succ_lt_succ hi⟩ = x ⟨i+1, hi⟩ := by simp [ih (f ·.succ)]; done
      conv => rhs; rw [← h]
      congr; simp [encodePi, Nat.mul_add_div h0, Nat.div_eq_of_lt (x 0).is_lt]; rfl

/-- Encode `{ i : Fin n // P i }` into `Fin (Fin.count P)` where `P` is a decidable predicate. -/
def encodeSubtype (P : Fin n → Prop) [inst : DecidablePred P] (i : { i // P i }) :
    Fin (Fin.count (P ·)) :=
  match n, P, inst, i with
  | n+1, P, inst, ⟨0, hp⟩ =>
    have : Fin.count (P ·) > 0 := by grind [count_succ]
    ⟨0, this⟩
  | n+1, P, inst, ⟨⟨i+1, hi⟩, hp⟩ =>
    match encodeSubtype (fun i => P i.succ) ⟨⟨i, Nat.lt_of_succ_lt_succ hi⟩, hp⟩ with
    | ⟨k, hk⟩ =>
      if h0 : P 0 then
        have : (Fin.count fun i => P i.succ) + 1 = Fin.count (P ·) := by
          grind [count_succ]
        Fin.cast this ⟨k+1, Nat.succ_lt_succ hk⟩
      else
        have : (Fin.count fun i => P i.succ) = Fin.count (P ·) := by simp [count_succ, h0]
        Fin.cast this ⟨k, hk⟩

/-- Decode `{ i : Fin n // P i }` from `Fin (Fin.count P)` where `P` is a decidable predicate. -/
def decodeSubtype (P : Fin n → Prop) [inst : DecidablePred P] (k : Fin (Fin.count (P ·))) :
    { i // P i } :=
  match n, P, inst, k with
  | 0, _, _, ⟨_, h⟩ => False.elim (by simp at h)
  | n+1, P, inst, ⟨k, hk⟩ =>
    if h0 : P 0 then
      have : Fin.count (P ·) = (Fin.count fun i => P i.succ) + 1 := by grind [count_succ]
      match k with
      | 0 => ⟨0, h0⟩
      | k + 1 =>
        match decodeSubtype (fun i => P i.succ) ⟨k, Nat.lt_of_add_lt_add_right (this ▸ hk)⟩ with
        | ⟨⟨i, hi⟩, hp⟩ => ⟨⟨i+1, Nat.succ_lt_succ hi⟩, hp⟩
    else
      have : Fin.count (P ·) = Fin.count fun i => P i.succ := by simp [count_succ, h0]
      match decodeSubtype (fun i => P (succ i)) ⟨k, this ▸ hk⟩ with
      | ⟨⟨i, hi⟩, hp⟩ => ⟨⟨i+1, Nat.succ_lt_succ hi⟩, hp⟩

theorem encodeSubtype_zero_pos {P : Fin (n+1) → Prop} [DecidablePred P] (h₀ : P 0) :
    encodeSubtype P ⟨0, h₀⟩ = ⟨0, by grind [count_succ]⟩ := by
  ext; rw [encodeSubtype.eq_def]; rfl

theorem encodeSubtype_succ_pos {P : Fin (n+1) → Prop} [DecidablePred P] (h₀ : P 0) {i : Fin n}
    (h : P i.succ) : encodeSubtype P ⟨i.succ, h⟩ =
      (encodeSubtype (fun i => P i.succ) ⟨i, h⟩).succ.cast (by grind [count_succ]) := by
  ext; rw [encodeSubtype.eq_def]; simp [Fin.succ, *]

theorem encodeSubtype_succ_neg {P : Fin (n+1) → Prop} [DecidablePred P] (h₀ : ¬ P 0) {i : Fin n}
    (h : P i.succ) : encodeSubtype P ⟨i.succ, h⟩ =
      (encodeSubtype (fun i => P i.succ) ⟨i, h⟩).cast (by simp [count_succ, *]) := by
  ext; rw [encodeSubtype.eq_def]; simp [Fin.succ, *]

@[simp] theorem encodeSubtype_decodeSubtype (P : Fin n → Prop) [DecidablePred P]
    (x : Fin (Fin.count (P ·))) : encodeSubtype P (decodeSubtype P x) = x := by
  induction n with
  | zero => absurd x.is_lt; simp
  | succ n ih =>
    simp only [decodeSubtype]
    split
    · ext; split <;> simp [encodeSubtype_zero_pos, encodeSubtype, *]; done
    · ext; simp [encodeSubtype, *]

@[simp] theorem decodeSubtype_encodeSubtype (P : Fin n → Prop) [DecidablePred P] (x : { x // P x}) :
    decodeSubtype P (encodeSubtype P x) = x := by
  match x with
  | ⟨i, h⟩ =>
    induction n with
    | zero => absurd x.val.is_lt; simp
    | succ n ih =>
      if h₀ : P 0 then
        simp only [decodeSubtype, dif_pos h₀]
        cases i using Fin.cases with
        | zero => rw [encodeSubtype_zero_pos h₀]
        | succ i =>
          rw [encodeSubtype_succ_pos h₀]
          simp only [coe_cast, val_succ, Subtype.mk.injEq]
          congr
          rw [ih (fun i => P i.succ) ⟨i, h⟩]
      else
        simp only [decodeSubtype, dif_neg h₀]
        cases i using Fin.cases with
        | zero => contradiction
        | succ i =>
          rw [encodeSubtype_succ_neg h₀]
          simp only [coe_cast, Subtype.mk.injEq]
          congr
          rw [ih (fun i => P i.succ) ⟨i, h⟩]

/-- Get representative for the equivalence class of `x`. -/
abbrev getRepr (s : Setoid (Fin n)) [DecidableRel s.r] (x : Fin n) : Fin n :=
  match h : Fin.find? (fun y => s.r x y) with
  | some y => y
  | none => False.elim <| by
    have : Fin.find? (fun y => s.r x y) |>.isSome := by
      rw [isSome_find?_iff]
      exists x
      apply decide_eq_true
      exact Setoid.refl x
    simp [h] at this

@[simp] theorem equiv_getRepr (s : Setoid (Fin n)) [DecidableRel s.r] (x : Fin n) :
    s.r x (getRepr s x) := by
  simp only [getRepr]
  split
  · next hsome =>
    apply of_decide_eq_true
    apply eq_true_of_find?_eq_some hsome
  · next hnone =>
    absurd s.refl x
    apply of_decide_eq_false
    apply eq_false_of_find?_eq_none hnone

@[simp] theorem getRepr_equiv (s : Setoid (Fin n)) [DecidableRel s.r] (x : Fin n) :
    s.r (getRepr s x) x := Setoid.symm (equiv_getRepr ..)

theorem getRepr_eq_getRepr_of_equiv (s : Setoid (Fin n)) [DecidableRel s.r] (h : s.r x y) :
    getRepr s x = getRepr s y := by
  have hfind : Fin.find? (s.r x ·) = Fin.find? (s.r y ·) := by
    congr
    funext z
    rw [decide_eq_decide]
    constructor
    · exact Setoid.trans (Setoid.symm h)
    · exact Setoid.trans h
  simp only [getRepr]
  split
  · next hx =>
    rw [hfind] at hx
    split
    · next hy =>
      rwa [hx, Option.some_inj] at hy
    · next hy =>
      rw [hx] at hy
      contradiction
  · next hx =>
    rw [hfind] at hx
    split
    · next hy =>
      rw [hx] at hy
      contradiction
    · rfl

@[simp] theorem getRepr_getRepr (s : Setoid (Fin n)) [DecidableRel s.r] (x : Fin n) :
    getRepr s (getRepr s x) = getRepr s x := by
  apply getRepr_eq_getRepr_of_equiv
  exact getRepr_equiv ..

/-- Encode `Quotient s` into `Fin m` where `s` is a decidable setoid on `Fin n`. -/
def encodeQuotient (s : Setoid (Fin n)) [DecidableRel s.r] (x : Quotient s) :
    Fin (Fin.count fun i => getRepr s i = i) :=
  encodeSubtype _ <| Quotient.liftOn x (fun i => ⟨getRepr s i, getRepr_getRepr s i⟩) <| by
    intro _ _ h
    simp only [Subtype.mk.injEq]
    exact getRepr_eq_getRepr_of_equiv s h

/-- Decode `Quotient s` from `Fin m` where `s` is a decidable setoid on `Fin n`. -/
def decodeQuotient (s : Setoid (Fin n)) [DecidableRel s.r]
    (i : Fin (Fin.count fun i => getRepr s i = i)) : Quotient s :=
  Quotient.mk s (decodeSubtype _ i)

@[simp] theorem encodeQuotient_decodeQuotient (s : Setoid (Fin n)) [DecidableRel s.r] (x) :
    encodeQuotient s (decodeQuotient s x) = x := by
  simp only [decodeQuotient, encodeQuotient, Quotient.liftOn, Quotient.mk, Quot.liftOn]
  conv => rhs; rw [← encodeSubtype_decodeSubtype _ x]
  congr
  exact (decodeSubtype _ x).property

@[simp] theorem decodeQuotient_encodeQuotient (s : Setoid (Fin n)) [DecidableRel s.r] (x) :
    decodeQuotient s (encodeQuotient s x) = x := by
  induction x using Quotient.inductionOn with
  | _ x =>
    simp only [decodeQuotient, encodeQuotient, Quotient.liftOn, Quotient.mk, Quot.liftOn]
    apply Quot.sound
    simp
