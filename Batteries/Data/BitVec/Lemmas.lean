/-
Copyright (c) 2024 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: François G. Dorais
-/

import Batteries.Data.BitVec.Basic
import Batteries.Data.Fin.OfBits
import Batteries.Data.Nat.Lemmas
import Batteries.Data.Int

namespace BitVec

@[simp] theorem toNat_ofFnLEAux (m : Nat) (f : Fin n → Bool) :
    (ofFnLEAux m f).toNat = Nat.ofBits f % 2 ^ m := by
  simp only [ofFnLEAux]
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Fin.foldr_succ, toNat_shiftConcat, Nat.shiftLeft_eq, Nat.pow_one, Nat.ofBits_succ, ih,
      ← Nat.mod_add_div (Nat.ofBits (f ∘ Fin.succ)) (2 ^ m), Nat.mul_add 2, Nat.add_right_comm,
      Nat.mul_left_comm, Nat.add_mul_mod_self_left, Nat.mul_comm 2]
    rfl

@[simp] theorem toFin_ofFnLEAux (m : Nat) (f : Fin n → Bool) :
    (ofFnLEAux m f).toFin = Fin.ofNat' (2 ^ m) (Nat.ofBits f) := by
  ext; simp

@[simp] theorem toNat_ofFnLE (f : Fin n → Bool) : (ofFnLE f).toNat = Nat.ofBits f := by
  rw [ofFnLE, toNat_ofFnLEAux, Nat.mod_eq_of_lt (Nat.ofBits_lt_two_pow f)]

@[simp] theorem toFin_ofFnLE (f : Fin n → Bool) : (ofFnLE f).toFin = Fin.ofBits f := by
  ext; simp

@[simp] theorem toInt_ofFnLE (f : Fin n → Bool) : (ofFnLE f).toInt = Int.ofBits f := by
  simp only [BitVec.toInt, Int.ofBits, toNat_ofFnLE, Int.subNatNat_eq_coe]; rfl

theorem getElem_ofFnLEAux (f : Fin n → Bool) (i) (h : i < n) (h' : i < m) :
    (ofFnLEAux m f)[i] = f ⟨i, h⟩ := by
  simp only [ofFnLEAux]
  induction n generalizing i m with
  | zero => contradiction
  | succ n ih =>
    simp only [Fin.foldr_succ, getElem_shiftConcat]
    cases i with
    | zero =>
      simp
    | succ i =>
      rw [ih (fun i => f i.succ)] <;> try omega
      simp

@[simp] theorem getElem_ofFnLE (f : Fin n → Bool) (i) (h : i < n) : (ofFnLE f)[i] = f ⟨i, h⟩ :=
  getElem_ofFnLEAux ..

theorem getLsb'_ofFnLE (f : Fin n → Bool) (i) : (ofFnLE f).getLsb' i = f i := by simp

theorem getLsbD_ofFnLE (f : Fin n → Bool) (i) :
    (ofFnLE f).getLsbD i = if h : i < n then f ⟨i, h⟩ else false := by
  split
  · next h => rw [getLsbD_eq_getElem h, getElem_ofFnLE]
  · next h => rw [getLsbD_ge _ _ (Nat.ge_of_not_lt h)]

@[simp] theorem getMsb'_ofFnLE (f : Fin n → Bool) (i) : (ofFnLE f).getMsb' i = f i.rev := by
  simp [getMsb'_eq_getLsb', Fin.rev]; congr 2; omega

theorem getMsbD_ofFnLE (f : Fin n → Bool) (i) :
    (ofFnLE f).getMsbD i = if h : i < n then f (Fin.rev ⟨i, h⟩) else false := by
  split
  · next h =>
    have heq : n - 1 - i = n - (i + 1) := by omega
    have hlt : n - (i + 1) < n := by omega
    simp [getMsbD_eq_getLsbD, getLsbD_ofFnLE, Fin.rev, h, heq, hlt]
  · next h => rw [getMsbD_ge _ _ (Nat.ge_of_not_lt h)]

theorem msb_ofFnLE (f : Fin n → Bool) :
    (ofFnLE f).msb = if h : n ≠ 0 then f ⟨n-1, Nat.sub_one_lt h⟩ else false := by
  cases n <;> simp [msb_eq_getMsbD_zero, getMsbD_ofFnLE, Fin.last]

@[simp] theorem toNat_ofFnBE (f : Fin n → Bool) : (ofFnBE f).toNat = Nat.ofBits (f ∘ Fin.rev) := by
  simp [ofFnBE]; rfl

@[simp] theorem toFin_ofFnBE (f : Fin n → Bool) : (ofFnBE f).toFin = Fin.ofBits (f ∘ Fin.rev) := by
  ext; simp

@[simp] theorem toInt_ofFnBE (f : Fin n → Bool) : (ofFnBE f).toInt = Int.ofBits (f ∘ Fin.rev) := by
  simp [ofFnBE]; rfl

@[simp] theorem getElem_ofFnBE (f : Fin n → Bool) (i) (h : i < n) :
    (ofFnBE f)[i] = f (Fin.rev ⟨i, h⟩) := by simp [ofFnBE]

theorem getLsb'_ofFnBE (f : Fin n → Bool) (i) : (ofFnBE f).getLsb' i = f i.rev := by
  simp

theorem getLsbD_ofFnBE (f : Fin n → Bool) (i) :
    (ofFnBE f).getLsbD i = if h : i < n then f (Fin.rev ⟨i, h⟩) else false := by
  simp [ofFnBE, getLsbD_ofFnLE]

@[simp] theorem getMsb'_ofFnBE (f : Fin n → Bool) (i) : (ofFnBE f).getMsb' i = f i := by
  simp [ofFnBE]

theorem getMsbD_ofFnBE (f : Fin n → Bool) (i) :
    (ofFnBE f).getMsbD i = if h : i < n then f ⟨i, h⟩ else false := by
  simp [ofFnBE, getMsbD_ofFnLE]

theorem msb_ofFnBE (f : Fin n → Bool) :
    (ofFnBE f).msb = if h : n ≠ 0 then f ⟨0, Nat.zero_lt_of_ne_zero h⟩ else false := by
  cases n <;> simp [ofFnBE, msb_ofFnLE, Fin.rev]
