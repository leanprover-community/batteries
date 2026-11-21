/-
Copyright (c) 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: François G. Dorais
-/
module

public import Batteries.Data.Float.Lemmas.Basic

/-!
# Sign and commutativity lemmas for `Float` and `Float32`

The lemmas are proved through the logical models `Float.Model` and `Float32.Model`.
-/

public section

namespace Float.Model.UnpackedFloat

namespace Sign

@[simp] theorem neg_neg (s : Sign) : - -s = s := by cases s <;> rfl

@[simp] protected theorem neg_mul (s t : Sign) : -s * t = -(s * t) := by cases s <;> cases t <;> rfl

@[simp] protected theorem mul_neg (s t : Sign) : s * -t = -(s * t) := by cases s <;> cases t <;> rfl

@[simp] protected theorem neg_div (s t : Sign) : -s / t = -(s / t) := by cases s <;> cases t <;> rfl

@[simp] protected theorem div_neg (s t : Sign) : s / -t = -(s / t) := by cases s <;> cases t <;> rfl

protected theorem mul_comm (s t : Sign) : s * t = t * s := by cases s <;> cases t <;> rfl

end Sign

@[simp] theorem neg_neg (u : UnpackedFloat) : u.neg.neg = u := by
  cases u <;> simp [neg]

theorem unpack_packComponents_neg {spec : Format} (s e m) :
    unpack spec (packComponents spec (-s) e m) = (unpack spec (packComponents spec s e m)).neg := by
  cases s <;>
  · simp only [unpack, unpackSign_packComponents, unpackExponent_packComponents,
      unpackMantissa_packComponents]
    split
    · split <;> rfl
    · split
      · split <;> rfl
      · rfl

/-- The bit pattern `b` with its sign bit flipped. -/
def flipSign {spec : Format} (b : BitVec spec.numBits) : BitVec spec.numBits :=
  packComponents spec (-Sign.ofBitVec (unpackSign b)) (unpackExponent b) (unpackMantissa b)

theorem unpack_flipSign {spec : Format} (b : BitVec spec.numBits) :
    unpack spec (flipSign b) = (unpack spec b).neg := by
  conv => rhs; rw [← packComponents_unpackSign_unpackExponent_unpackMantissa b]
  exact unpack_packComponents_neg ..

@[simp] theorem unpack_pack_neg_unpack {spec : Format} (b : BitVec spec.numBits) :
    unpack spec (pack spec (unpack spec b).neg) = (unpack spec b).neg := by
  rw [← unpack_flipSign, unpack_pack_unpack]

theorem flipSign_packComponents {spec : Format} (s e m) :
    flipSign (packComponents spec s e m) = packComponents spec (-s) e m := by
  simp [flipSign]

/-- Packing commutes with negation, except on NaN. -/
theorem pack_neg {spec : Format} {u : UnpackedFloat} (h : u ≠ notANumber) :
    pack spec u.neg = flipSign (pack spec u) := by
  cases u with
  | notANumber => contradiction
  | infinity s => simp [neg, pack, packedInfinity, flipSign_packComponents]
  | zero s => simp [neg, pack, packedZero, flipSign_packComponents]
  | finite s m e hm =>
    simp only [neg, pack]
    split
    · simp [packedInfinity, flipSign_packComponents]
    · split <;> simp [flipSign_packComponents]

theorem roundWithAccuracy_neg (spec : Format) (s m e a) :
    roundWithAccuracy spec (-s) m e a = (roundWithAccuracy spec s m e a).neg := by
  simp only [roundWithAccuracy]
  split <;> simp [neg]

protected theorem neg_mul (spec : Format) (u v : UnpackedFloat) :
    mul spec u.neg v = (mul spec u v).neg := by
  cases u <;> cases v <;> simp [neg, mul, roundWithAccuracy_neg]

protected theorem mul_neg (spec : Format) (u v : UnpackedFloat) :
    mul spec u v.neg = (mul spec u v).neg := by
  cases u <;> cases v <;> simp [neg, mul, roundWithAccuracy_neg]

protected theorem neg_div (spec : Format) (u v : UnpackedFloat) :
    div spec u.neg v = (div spec u v).neg := by
  cases u <;> cases v <;> simp [neg, div, roundWithAccuracy_neg]

protected theorem div_neg (spec : Format) (u v : UnpackedFloat) :
    div spec u v.neg = (div spec u v).neg := by
  cases u <;> cases v <;> simp [neg, div, roundWithAccuracy_neg]

protected theorem mul_comm (spec : Format) (u v : UnpackedFloat) :
    mul spec u v = mul spec v u := by
  cases u <;> cases v <;> simp [mul, Sign.mul_comm, Nat.mul_comm, Int.add_comm]

protected theorem add_comm (spec : Format) (u v : UnpackedFloat) :
    add spec u v = add spec v u := by
  cases u <;> cases v <;> simp only [add]
  · rename_i s t; cases s <;> cases t <;> rfl
  · rename_i s t; cases s <;> cases t <;> rfl
  · rw [Int.min_comm, Int.add_comm]

end Float.Model.UnpackedFloat

namespace Float.Model

theorem unpack_pack_unpack (a : Float.Model) : (pack a.unpack).unpack = a.unpack := by
  simp [pack, unpack]

theorem unpack_pack_neg_unpack (a : Float.Model) :
    (pack a.unpack.neg).unpack = a.unpack.neg := by
  simp [pack, unpack]

theorem pack_unpack (a : Float.Model) : pack a.unpack = a := by
  rcases a with ⟨⟨b⟩, h⟩
  simp only [pack, unpack]
  congr 2
  exact UnpackedFloat.pack_unpack_of_valid h

/-- Negation of a packed float. -/
theorem neg_pack (u : UnpackedFloat) : -(pack u) = pack u.neg := by
  by_cases h : u = .notANumber
  · subst h; rfl
  · change pack (pack u).unpack.neg = pack u.neg
    have : (pack u).unpack.neg = (pack u.neg).unpack := by
      simp only [pack, unpack, UInt64.toBitVec_ofBitVec, UnpackedFloat.pack_neg h,
        UnpackedFloat.unpack_flipSign]
    rw [this, pack_unpack]

@[simp] theorem neg_neg (a : Float.Model) : - -a = a := by
  change pack (pack a.unpack.neg).unpack.neg = a
  rw [unpack_pack_neg_unpack, UnpackedFloat.neg_neg, pack_unpack]

protected theorem neg_mul (a b : Float.Model) : -a * b = -(a * b) := by
  change pack (UnpackedFloat.mul _ (pack a.unpack.neg).unpack b.unpack) = -(pack _)
  rw [unpack_pack_neg_unpack, UnpackedFloat.neg_mul, neg_pack]

protected theorem mul_neg (a b : Float.Model) : a * -b = -(a * b) := by
  change pack (UnpackedFloat.mul _ a.unpack (pack b.unpack.neg).unpack) = -(pack _)
  rw [unpack_pack_neg_unpack, UnpackedFloat.mul_neg, neg_pack]

protected theorem neg_div (a b : Float.Model) : -a / b = -(a / b) := by
  change pack (UnpackedFloat.div _ (pack a.unpack.neg).unpack b.unpack) = -(pack _)
  rw [unpack_pack_neg_unpack, UnpackedFloat.neg_div, neg_pack]

protected theorem div_neg (a b : Float.Model) : a / -b = -(a / b) := by
  change pack (UnpackedFloat.div _ a.unpack (pack b.unpack.neg).unpack) = -(pack _)
  rw [unpack_pack_neg_unpack, UnpackedFloat.div_neg, neg_pack]

protected theorem mul_comm (a b : Float.Model) : a * b = b * a := by
  change pack (UnpackedFloat.mul _ a.unpack b.unpack) = pack (UnpackedFloat.mul _ b.unpack a.unpack)
  rw [UnpackedFloat.mul_comm]

protected theorem add_comm (a b : Float.Model) : a + b = b + a := by
  change pack (UnpackedFloat.add _ a.unpack b.unpack) = pack (UnpackedFloat.add _ b.unpack a.unpack)
  rw [UnpackedFloat.add_comm]

end Float.Model

namespace Float

@[simp] theorem neg_neg (x : Float) : - -x = x := by
  change ofModel (- -x.toModel) = x
  rw [Model.neg_neg]

@[simp] protected theorem neg_mul (x y : Float) : -x * y = -(x * y) := by
  change ofModel (-x.toModel * y.toModel) = ofModel (-(x.toModel * y.toModel))
  rw [Model.neg_mul]

@[simp] protected theorem mul_neg (x y : Float) : x * -y = -(x * y) := by
  change ofModel (x.toModel * -y.toModel) = ofModel (-(x.toModel * y.toModel))
  rw [Model.mul_neg]

@[simp] protected theorem neg_div (x y : Float) : -x / y = -(x / y) := by
  change ofModel (-x.toModel / y.toModel) = ofModel (-(x.toModel / y.toModel))
  rw [Model.neg_div]

@[simp] protected theorem div_neg (x y : Float) : x / -y = -(x / y) := by
  change ofModel (x.toModel / -y.toModel) = ofModel (-(x.toModel / y.toModel))
  rw [Model.div_neg]

protected theorem mul_comm (x y : Float) : x * y = y * x := by
  change ofModel (x.toModel * y.toModel) = ofModel (y.toModel * x.toModel)
  rw [Model.mul_comm]

protected theorem add_comm (x y : Float) : x + y = y + x := by
  change ofModel (x.toModel + y.toModel) = ofModel (y.toModel + x.toModel)
  rw [Model.add_comm]

end Float

namespace Float32.Model

open Float.Model

theorem unpack_pack_unpack (a : Float32.Model) : (pack a.unpack).unpack = a.unpack := by
  simp [pack, unpack]

theorem unpack_pack_neg_unpack (a : Float32.Model) :
    (pack a.unpack.neg).unpack = a.unpack.neg := by
  simp [pack, unpack]

theorem pack_unpack (a : Float32.Model) : pack a.unpack = a := by
  rcases a with ⟨⟨b⟩, h⟩
  simp only [pack, unpack]
  congr 2
  exact UnpackedFloat.pack_unpack_of_valid h

/-- Negation of a packed float. -/
theorem neg_pack (u : UnpackedFloat) : -(pack u) = pack u.neg := by
  by_cases h : u = .notANumber
  · subst h; rfl
  · change pack (pack u).unpack.neg = pack u.neg
    have : (pack u).unpack.neg = (pack u.neg).unpack := by
      simp only [pack, unpack, UInt32.toBitVec_ofBitVec, UnpackedFloat.pack_neg h,
        UnpackedFloat.unpack_flipSign]
    rw [this, pack_unpack]

@[simp] theorem neg_neg (a : Float32.Model) : - -a = a := by
  change pack (pack a.unpack.neg).unpack.neg = a
  rw [unpack_pack_neg_unpack, UnpackedFloat.neg_neg, pack_unpack]

protected theorem neg_mul (a b : Float32.Model) : -a * b = -(a * b) := by
  change pack (UnpackedFloat.mul _ (pack a.unpack.neg).unpack b.unpack) = -(pack _)
  rw [unpack_pack_neg_unpack, UnpackedFloat.neg_mul, neg_pack]

protected theorem mul_neg (a b : Float32.Model) : a * -b = -(a * b) := by
  change pack (UnpackedFloat.mul _ a.unpack (pack b.unpack.neg).unpack) = -(pack _)
  rw [unpack_pack_neg_unpack, UnpackedFloat.mul_neg, neg_pack]

protected theorem neg_div (a b : Float32.Model) : -a / b = -(a / b) := by
  change pack (UnpackedFloat.div _ (pack a.unpack.neg).unpack b.unpack) = -(pack _)
  rw [unpack_pack_neg_unpack, UnpackedFloat.neg_div, neg_pack]

protected theorem div_neg (a b : Float32.Model) : a / -b = -(a / b) := by
  change pack (UnpackedFloat.div _ a.unpack (pack b.unpack.neg).unpack) = -(pack _)
  rw [unpack_pack_neg_unpack, UnpackedFloat.div_neg, neg_pack]

protected theorem mul_comm (a b : Float32.Model) : a * b = b * a := by
  change pack (UnpackedFloat.mul _ a.unpack b.unpack) = pack (UnpackedFloat.mul _ b.unpack a.unpack)
  rw [UnpackedFloat.mul_comm]

protected theorem add_comm (a b : Float32.Model) : a + b = b + a := by
  change pack (UnpackedFloat.add _ a.unpack b.unpack) = pack (UnpackedFloat.add _ b.unpack a.unpack)
  rw [UnpackedFloat.add_comm]

end Float32.Model

namespace Float32

@[simp] theorem neg_neg (x : Float32) : - -x = x := by
  change ofModel (- -x.toModel) = x
  rw [Model.neg_neg]

@[simp] protected theorem neg_mul (x y : Float32) : -x * y = -(x * y) := by
  change ofModel (-x.toModel * y.toModel) = ofModel (-(x.toModel * y.toModel))
  rw [Model.neg_mul]

@[simp] protected theorem mul_neg (x y : Float32) : x * -y = -(x * y) := by
  change ofModel (x.toModel * -y.toModel) = ofModel (-(x.toModel * y.toModel))
  rw [Model.mul_neg]

@[simp] protected theorem neg_div (x y : Float32) : -x / y = -(x / y) := by
  change ofModel (-x.toModel / y.toModel) = ofModel (-(x.toModel / y.toModel))
  rw [Model.neg_div]

@[simp] protected theorem div_neg (x y : Float32) : x / -y = -(x / y) := by
  change ofModel (x.toModel / -y.toModel) = ofModel (-(x.toModel / y.toModel))
  rw [Model.div_neg]

protected theorem mul_comm (x y : Float32) : x * y = y * x := by
  change ofModel (x.toModel * y.toModel) = ofModel (y.toModel * x.toModel)
  rw [Model.mul_comm]

protected theorem add_comm (x y : Float32) : x + y = y + x := by
  change ofModel (x.toModel + y.toModel) = ofModel (y.toModel + x.toModel)
  rw [Model.add_comm]

end Float32
