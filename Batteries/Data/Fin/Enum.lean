/-
Copyright (c) 2024 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: François G. Dorais
-/
import Batteries.Data.Fin.Coding

namespace Fin

/-- Class of types that are in bijection with a `Fin` type. -/
protected class Enum (α : Type _) where
  /-- Size of type. -/
  size : Nat
  /-- Enumeration of the type elements. -/
  decode : Fin size → α
  /-- Find the index of a type element. -/
  encode : α → Fin size
  /-- Inverse relation for `decode` and `encode`. -/
  decode_encode (x) : decode (encode x) = x
  /-- Inverse relation for `decode` and `encode`. -/
  encode_decode (i) : encode (decode i) = i

attribute [simp] Enum.decode_encode Enum.encode_decode

namespace Enum

instance : Fin.Enum Empty where
  size := 0
  decode := nofun
  encode := nofun
  decode_encode := nofun
  encode_decode := nofun

instance : Fin.Enum PUnit where
  size := 1
  decode := decodePUnit
  encode := encodePUnit
  decode_encode := decodePUnit_encodePUnit
  encode_decode := encodePUnit_decodePUnit

instance : Fin.Enum Bool where
  size := 2
  decode := decodeBool
  encode := encodeBool
  decode_encode := decodeBool_encodeBool
  encode_decode := encodeBool_decodeBool

instance : Fin.Enum Char where
  size := 1112064
  decode := decodeChar
  encode := encodeChar
  decode_encode := decodeChar_encodeChar
  encode_decode := encodeChar_decodeChar

instance [Fin.Enum α] : Fin.Enum (Option α) where
  size := size α + 1
  decode i := decodeOption i |>.map decode
  encode x := encodeOption <| x.map encode
  decode_encode := by simp [Function.comp_def]
  encode_decode := by simp [Function.comp_def]

instance [Fin.Enum α] [Fin.Enum β] : Fin.Enum (α ⊕ β) where
  size := size α + size β
  decode i :=
    match decodeSum i with
    | .inl i => .inl <| decode i
    | .inr i => .inr <| decode i
  encode x :=
    match x with
    | .inl x => encodeSum <| .inl (encode x)
    | .inr x => encodeSum <| .inr (encode x)
  decode_encode _ := by
    split
    · next h =>
      split at h;
      · simp at h; cases h; simp
      · simp at h
    · next h =>
      split at h;
      · simp at h
      · simp at h; cases h; simp
  encode_decode _ := by
    split
    · next h =>
      split at h
      · next h' => cases h; simp [← h']
      · simp at h
    · next h =>
      split at h
      · simp at h
      · next h' => cases h; simp [← h']

instance [Fin.Enum α] [Fin.Enum β] : Fin.Enum (α × β) where
  size := size α * size β
  decode i := (decode (decodeProd i).fst, decode (decodeProd i).snd)
  encode x := encodeProd (encode x.fst, encode x.snd)
  encode_decode := by simp [Prod.eta]
  decode_encode := by simp

instance [Fin.Enum α] [Fin.Enum β] : Fin.Enum (β → α) where
  size := size α ^ size β
  decode i x := decode (decodeFun i (encode x))
  encode f := encodeFun fun x => encode (f (decode x))
  encode_decode := by simp
  decode_encode := by simp

instance (β : α → Type _) [Fin.Enum α] [(x : α) → Fin.Enum (β x)] : Fin.Enum ((x : α) × β x) where
  size := Fin.sum fun i => size (β (decode i))
  decode i :=
    match decodeSigma _ i with
    | ⟨i, j⟩ => ⟨decode i, decode j⟩
  encode | ⟨x, y⟩ => encodeSigma _ ⟨encode x, encode (_root_.cast (by simp) y)⟩
  encode_decode i := by
    simp only []
    conv => rhs; rw [← encodeSigma_decodeSigma _ i]
    congr 1
    ext
    · simp
    · simp only []
      conv => rhs; rw [← encode_decode (decodeSigma _ i).snd]
      congr <;> simp
  decode_encode
  | ⟨x, y⟩ => by
    ext
    simp only [cast, decodeSigma_encodeSigma, decode_encode]
    simp []
    rw [decodeSigma_encodeSigma]
    simp

instance (β : α → Type _) [Fin.Enum α] [(x : α) → Fin.Enum (β x)] : Fin.Enum ((x : α) → β x) where
  size := Fin.prod fun i => size (β (decode i))
  decode i x := decode <| (decodePi _ i (encode x)).cast (by rw [decode_encode])
  encode f := encodePi _ fun i => encode (f (decode i))
  encode_decode i := by
    simp only [encode_decode]
    conv => rhs; rw [← encodePi_decodePi _ i]
    congr
    ext
    simp only [coe_cast]
    rw [encode_decode]
  decode_encode f := by
    funext x
    conv => rhs; rw [← decode_encode (f x)]
    congr 1
    ext
    simp only [decodePi_encodePi, coe_cast]
    rw [decode_encode]

instance (P : α → Prop) [DecidablePred P] [Fin.Enum α] : Fin.Enum { x // P x} where
  size := Fin.count fun i => P (decode i)
  decode i := ⟨decode (decodeSubtype _ i).val, (decodeSubtype _ i).property⟩
  encode x := encodeSubtype _ ⟨encode x.val, (decode_encode x.val).symm ▸ x.property⟩
  encode_decode i := by simp [Subtype.eta]
  decode_encode := by simp

private def decodeSetoid (s : Setoid α) [DecidableRel s.r] [Fin.Enum α] :
    Setoid (Fin (size α)) where
  r i j := s.r (decode i) (decode j)
  iseqv := {
    refl := fun i => Setoid.refl (decode i)
    symm := Setoid.symm
    trans := Setoid.trans
  }

private instance (s : Setoid α) [DecidableRel s.r] [Fin.Enum α] : DecidableRel (decodeSetoid s).r :=
  fun _ _ => inferInstanceAs (Decidable (s.r _ _))

instance (s : Setoid α) [DecidableRel s.r] [Fin.Enum α] : Fin.Enum (Quotient s) where
  size := Fin.count fun i => getRepr (decodeSetoid s) i = i
  decode i := Quotient.liftOn (decodeQuotient (decodeSetoid s) i)
    (fun i => Quotient.mk s (decode i)) (fun _ _ h => Quotient.sound h)
  encode x := Quotient.liftOn x
    (fun x => encodeQuotient (decodeSetoid s) (Quotient.mk _ (encode x))) <| by
      intro _ _ h
      simp only []
      congr 1
      apply Quotient.sound
      simp only [HasEquiv.Equiv, decodeSetoid, decode_encode]
      exact h
  decode_encode x := by
    induction x using Quotient.inductionOn with
    | _ x =>
      simp only [decodeQuotient, encodeQuotient, decodeSubtype_encodeSubtype, Quotient.liftOn,
        Quotient.mk, Quot.liftOn]
      apply Quot.sound
      conv => rhs; rw [← decode_encode x]
      exact getRepr_equiv (decodeSetoid s) ..
  encode_decode i := by
    conv => rhs; rw [← encodeSubtype_decodeSubtype _ i]
    simp only [Quotient.liftOn, Quot.liftOn, encodeQuotient, Quotient.mk, decodeQuotient,
      encode_decode]
    congr
    rw [(decodeSubtype _ i).property]
