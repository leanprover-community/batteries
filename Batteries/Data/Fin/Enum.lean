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
  enum : Fin size → α
  /-- Find the index of a type element. -/
  find : α → Fin size
  /-- Inverse relation for `enum` and `find`. -/
  enum_find (x) : enum (find x) = x
  /-- Inverse relation for `enum` and `find`. -/
  find_enum (i) : find (enum i) = i

attribute [simp] Enum.enum_find Enum.find_enum

namespace Enum

instance : Fin.Enum Empty where
  size := 0
  enum := nofun
  find := nofun
  enum_find := nofun
  find_enum := nofun

instance : Fin.Enum PUnit where
  size := 1
  enum := decodePUnit
  find := encodePUnit
  enum_find := decodePUnit_encodePUnit
  find_enum := encodePUnit_decodePUnit

instance : Fin.Enum Bool where
  size := 2
  enum := decodeBool
  find := encodeBool
  enum_find := decodeBool_encodeBool
  find_enum := encodeBool_decodeBool

instance [Fin.Enum α] : Fin.Enum (Option α) where
  size := size α + 1
  enum i := decodeOption i |>.map enum
  find x := encodeOption <| x.map find
  enum_find := by simp [Function.comp_def]
  find_enum := by simp [Function.comp_def]

instance [Fin.Enum α] [Fin.Enum β] : Fin.Enum (α ⊕ β) where
  size := size α + size β
  enum i :=
    match decodeSum i with
    | .inl i => .inl <| enum i
    | .inr i => .inr <| enum i
  find x :=
    match x with
    | .inl x => encodeSum <| .inl (find x)
    | .inr x => encodeSum <| .inr (find x)
  enum_find _ := by
    simp only; split
    · next h =>
      split at h;
      · simp at h; cases h; simp
      · simp at h
    · next h =>
      split at h;
      · simp at h
      · simp at h; cases h; simp
  find_enum _ := by
    simp only; split
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
  enum i := (enum (decodeProd i).fst, enum (decodeProd i).snd)
  find x := encodeProd (find x.fst, find x.snd)
  find_enum := by simp [Prod.eta]
  enum_find := by simp

instance [Fin.Enum α] [Fin.Enum β] : Fin.Enum (β → α) where
  size := size α ^ size β
  enum i x := enum (decodeFun i (find x))
  find f := encodeFun fun x => find (f (enum x))
  find_enum := by simp
  enum_find := by simp

instance (β : α → Type _) [Fin.Enum α] [(x : α) → Fin.Enum (β x)] : Fin.Enum ((x : α) × β x) where
  size := Fin.sum fun i => size (β (enum i))
  enum i :=
    match decodeSigma _ i with
    | ⟨i, j⟩ => ⟨enum i, enum j⟩
  find | ⟨x, y⟩ => encodeSigma _ ⟨find x, find (_root_.cast (by simp) y)⟩
  find_enum i := by
    simp only []
    conv => rhs; rw [← encodeSigma_decodeSigma _ i]
    congr 1
    ext
    · simp
    · simp only []
      conv => rhs; rw [← find_enum (decodeSigma _ i).snd]
      congr <;> simp
  enum_find
  | ⟨x, y⟩ => by
    ext
    simp only [cast, decodeSigma_encodeSigma, enum_find]
    simp []
    rw [decodeSigma_encodeSigma]
    simp

instance (β : α → Type _) [Fin.Enum α] [(x : α) → Fin.Enum (β x)] : Fin.Enum ((x : α) → β x) where
  size := Fin.prod fun i => size (β (enum i))
  enum i x := enum <| (decodePi _ i (find x)).cast (by rw [enum_find])
  find f := encodePi _ fun i => find (f (enum i))
  find_enum i := by
    simp only [find_enum]
    conv => rhs; rw [← encodePi_decodePi _ i]
    congr
    ext
    simp only [cast]
    rw [find_enum]
  enum_find f := by
    funext x
    simp only []
    conv => rhs; rw [← enum_find (f x)]
    congr 1
    ext
    simp only [cast, decodePi_encodePi]
    rw [enum_find]
    done

instance (P : α → Prop) [DecidablePred P] [Fin.Enum α] : Fin.Enum { x // P x} where
  size := Fin.count fun i => P (enum i)
  enum i := ⟨enum (decodeSubtype _ i).val, (decodeSubtype _ i).property⟩
  find x := encodeSubtype _ ⟨find x.val, (enum_find x.val).symm ▸ x.property⟩
  find_enum i := by simp [Subtype.eta]
  enum_find := by simp

private def enumSetoid (s : Setoid α) [DecidableRel s.r] [Fin.Enum α] :
    Setoid (Fin (size α)) where
  r i j := s.r (enum i) (enum j)
  iseqv := {
    refl := fun i => Setoid.refl (enum i)
    symm := Setoid.symm
    trans := Setoid.trans
  }

private instance (s : Setoid α) [DecidableRel s.r] [Fin.Enum α] : DecidableRel (enumSetoid s).r :=
  fun _ _ => inferInstanceAs (Decidable (s.r _ _))

instance (s : Setoid α) [DecidableRel s.r] [Fin.Enum α] : Fin.Enum (Quotient s) where
  size := Fin.count fun i => getRepr (enumSetoid s) i = i
  enum i := Quotient.liftOn (decodeQuotient (enumSetoid s) i) (fun i => Quotient.mk s (enum i))
    (fun _ _ h => Quotient.sound h)
  find x := Quotient.liftOn x
    (fun x => encodeQuotient (enumSetoid s) (Quotient.mk _ (find x))) <| by
      intro _ _ h
      simp only []
      congr 1
      apply Quotient.sound
      simp only [HasEquiv.Equiv, enumSetoid, enum_find]
      exact h
  enum_find x := by
    induction x using Quotient.inductionOn with
    | _ x =>
      simp only [decodeQuotient, encodeQuotient, decodeSubtype_encodeSubtype, Quotient.liftOn,
        Quotient.mk, Quot.liftOn]
      apply Quot.sound
      conv => rhs; rw [← enum_find x]
      exact getRepr_equiv (enumSetoid s) ..
  find_enum i := by
    conv => rhs; rw [← encodeSubtype_decodeSubtype _ i]
    simp only [Quotient.liftOn, Quot.liftOn, encodeQuotient, Quotient.mk, decodeQuotient,
      find_enum]
    congr
    rw [(decodeSubtype _ i).property]
