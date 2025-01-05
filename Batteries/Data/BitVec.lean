/-
Copyright (c) 2024 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: François G. Dorais
-/

import Batteries.Data.Fin.OfBits

namespace BitVec

theorem getElem_shiftConcat (v : BitVec n) (b : Bool) (i) (h : i < n) :
    (v.shiftConcat b)[i] = if i = 0 then b else v[i-1] := by
  rw [← getLsbD_eq_getElem, getLsbD_shiftConcat, getLsbD_eq_getElem, decide_eq_true h,
    Bool.true_and]

@[simp] theorem getElem_shiftConcat_zero (v : BitVec n) (b : Bool) (h : 0 < n) :
    (v.shiftConcat b)[0] = b := by simp [getElem_shiftConcat]

@[simp] theorem getElem_shiftConcat_succ (v : BitVec n) (b : Bool) (h : i + 1 < n) :
    (v.shiftConcat b)[i+1] = v[i] := by simp [getElem_shiftConcat]

/-- `ofFnLEAux f` returns the `BitVec m` whose `i`th bit is `f i` when `i < m`, little endian. -/
@[inline] def ofFnLEAux (m : Nat) (f : Fin n → Bool) : BitVec m :=
  Fin.foldr n (fun i v => v.shiftConcat (f i)) 0

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

/-- `ofFnLE f` returns the `BitVec n` whose `i`th bit is `f i` with little endian ordering. -/
@[inline] def ofFnLE (f : Fin n → Bool) : BitVec n := ofFnLEAux n f

@[simp] theorem toNat_ofFnLE (f : Fin n → Bool) : (ofFnLE f).toNat = Nat.ofBits f := by
  rw [ofFnLE, toNat_ofFnLEAux, Nat.mod_eq_of_lt (Nat.ofBits_lt_two_pow f)]

@[simp] theorem toFin_ofFnLE (f : Fin n → Bool) : (ofFnLE f).toFin = Fin.ofBits f := by
  ext; simp

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

@[simp] theorem getMsb'_ofFnLE (f : Fin n → Bool) (i) : (ofFnLE f).getMsb' i = f i.rev := by
  simp [getMsb'_eq_getLsb', Fin.rev]; congr 2; omega

/-- `ofFnBE f` returns the `BitVec n` whose `i`th bit is `f i` with big endian ordering. -/
@[inline] def ofFnBE (f : Fin n → Bool) : BitVec n := ofFnLE fun i => f i.rev

@[simp] theorem toNat_ofFnBE (f : Fin n → Bool) : (ofFnBE f).toNat = Nat.ofBits (f ∘ Fin.rev) := by
  simp [ofFnBE]; rfl

@[simp] theorem toFin_ofFnBE (f : Fin n → Bool) : (ofFnBE f).toFin = Fin.ofBits (f ∘ Fin.rev) := by
  ext; simp

@[simp] theorem getElem_ofFnBE (f : Fin n → Bool) (i) (h : i < n) :
    (ofFnBE f)[i] = f (Fin.rev ⟨i, h⟩) := by simp [ofFnBE]

theorem getLsb'_ofFnBE (f : Fin n → Bool) (i) : (ofFnBE f).getLsb' i = f i.rev := by
  simp

@[simp] theorem getMsb'_ofFnBE (f : Fin n → Bool) (i) : (ofFnBE f).getMsb' i = f i := by
  simp [ofFnBE]
