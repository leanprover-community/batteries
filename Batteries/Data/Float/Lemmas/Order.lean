/-
Copyright (c) 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: François G. Dorais
-/
module

public import Batteries.Data.Float.Lemmas.Arithmetic

/-!
# Order lemmas for `Float` and `Float32`

The lemmas are proved through the logical models `Float.Model` and `Float32.Model`. The order is
the IEEE 754 partial order, in which `NaN` is incomparable with everything and `-0 = +0`.
-/

public section

namespace Float.Model.UnpackedFloat

namespace Sign

theorem compare_def (s t : Sign) : compare s t =
    match s, t with
    | .negative, .positive => .lt | .positive, .negative => .gt | _, _ => .eq := by
  cases s <;> cases t <;> rfl

end Sign

local macro "cases_uf " a:ident : tactic =>
  `(tactic| rcases $a:ident with ⟨_|_⟩ | _ | ⟨_|_⟩ | ⟨_|_, _, _, _⟩)

section

attribute [local simp] Sign.compare_def UnpackedFloat.compare UnpackedFloat.lt UnpackedFloat.le
  Ordering.then_eq_lt Ordering.then_eq_gt Ordering.swap_eq_lt Ordering.swap_eq_gt
  Int.compare_eq_lt Int.compare_eq_gt Int.compare_eq_eq Nat.compare_eq_lt Nat.compare_eq_gt
  Nat.compare_eq_eq Ordering.isLE_iff_eq_lt_or_eq_eq Ordering.isGE_iff_eq_gt_or_eq_eq
  Ordering.swap_eq_eq Ordering.then_eq_eq Ordering.swap_then Int.compare_swap Nat.compare_swap

theorem compare_swap (a b : UnpackedFloat) :
    b.compare a = (a.compare b).map Ordering.swap := by
  cases_uf a <;> cases_uf b <;> simp

protected theorem lt_irrefl (a : UnpackedFloat) : ¬ a.lt a := by
  cases_uf a <;> simp

protected theorem lt_asymm {a b : UnpackedFloat} : a.lt b → ¬ b.lt a := by
  cases_uf a <;> cases_uf b <;> simp <;> lia

protected theorem lt_trans {a b c : UnpackedFloat} : a.lt b → b.lt c → a.lt c := by
  cases_uf a <;> cases_uf b <;> cases_uf c <;> simp <;> lia

protected theorem le_trans {a b c : UnpackedFloat} : a.le b → b.le c → a.le c := by
  cases_uf a <;> cases_uf b <;> cases_uf c <;> simp <;> lia

protected theorem lt_of_lt_of_le {a b c : UnpackedFloat} : a.lt b → b.le c → a.lt c := by
  cases_uf a <;> cases_uf b <;> cases_uf c <;> simp <;> lia

protected theorem lt_of_le_of_lt {a b c : UnpackedFloat} : a.le b → b.lt c → a.lt c := by
  cases_uf a <;> cases_uf b <;> cases_uf c <;> simp <;> lia

protected theorem le_of_lt {a b : UnpackedFloat} : a.lt b → a.le b := by
  cases_uf a <;> cases_uf b <;> simp <;> lia

protected theorem lt_iff_le_not_ge {a b : UnpackedFloat} : a.lt b ↔ a.le b ∧ ¬ b.le a := by
  cases_uf a <;> cases_uf b <;> simp <;> lia

theorem le_refl_iff {a : UnpackedFloat} : a.le a ↔ a ≠ notANumber := by
  cases_uf a <;> simp

protected theorem not_le {a b : UnpackedFloat} (ha : a ≠ notANumber) (hb : b ≠ notANumber) :
    ¬ a.le b ↔ b.lt a := by
  cases_uf a <;> cases_uf b <;> simp at ha hb ⊢ <;> lia

@[simp] theorem notANumber_le (a : UnpackedFloat) : notANumber.le a = false := rfl
@[simp] theorem le_notANumber (a : UnpackedFloat) : a.le notANumber = false := by cases a <;> rfl
@[simp] theorem notANumber_lt (a : UnpackedFloat) : notANumber.lt a = false := rfl
@[simp] theorem lt_notANumber (a : UnpackedFloat) : a.lt notANumber = false := by cases a <;> rfl

theorem neg_lt_neg (a b : UnpackedFloat) : a.neg.lt b.neg = b.lt a := by
  cases_uf a <;> cases_uf b <;> simp [neg] <;> lia

theorem neg_le_neg (a b : UnpackedFloat) : a.neg.le b.neg = b.le a := by
  cases_uf a <;> cases_uf b <;> simp [neg] <;> lia

theorem minimum_comm (a b : UnpackedFloat) : a.minimum b = b.minimum a := by
  cases_uf a <;> cases_uf b <;> simp [minimum] <;> split <;> split <;>
    first | rfl | (exfalso; lia) | (congr 1 <;> lia)

theorem maximum_comm (a b : UnpackedFloat) : a.maximum b = b.maximum a := by
  cases_uf a <;> cases_uf b <;> simp [maximum] <;> split <;> split <;>
    first | rfl | (exfalso; lia) | (congr 1 <;> lia)

end

end Float.Model.UnpackedFloat

namespace Float.Model

theorem lt_iff_unpack_lt {a b : Float.Model} : a < b ↔ a.unpack.lt b.unpack := Iff.rfl

theorem le_iff_unpack_le {a b : Float.Model} : a ≤ b ↔ a.unpack.le b.unpack := Iff.rfl

theorem eq_nan_iff_unpack_eq {a : Float.Model} : a = nan ↔ a.unpack = .notANumber := by
  constructor
  · rintro rfl; simp [nan, unpack, pack, UnpackedFloat.pack]
  · intro h; rw [← pack_unpack a, h]; rfl

theorem unpack_neg (a : Float.Model) : (-a).unpack = a.unpack.neg := unpack_pack_neg_unpack a

protected theorem lt_irrefl (a : Float.Model) : ¬a < a := UnpackedFloat.lt_irrefl _

protected theorem lt_asymm {a b : Float.Model} : a < b → ¬b < a := UnpackedFloat.lt_asymm

protected theorem lt_trans {a b c : Float.Model} : a < b → b < c → a < c := UnpackedFloat.lt_trans

protected theorem le_trans {a b c : Float.Model} : a ≤ b → b ≤ c → a ≤ c := UnpackedFloat.le_trans

protected theorem lt_of_lt_of_le {a b c : Float.Model} : a < b → b ≤ c → a < c :=
  UnpackedFloat.lt_of_lt_of_le

protected theorem lt_of_le_of_lt {a b c : Float.Model} : a ≤ b → b < c → a < c :=
  UnpackedFloat.lt_of_le_of_lt

protected theorem le_of_lt {a b : Float.Model} : a < b → a ≤ b := UnpackedFloat.le_of_lt

protected theorem lt_iff_le_not_ge {a b : Float.Model} : a < b ↔ a ≤ b ∧ ¬b ≤ a :=
  UnpackedFloat.lt_iff_le_not_ge

theorem le_refl_iff {a : Float.Model} : a ≤ a ↔ a ≠ nan := by
  rw [ne_eq, eq_nan_iff_unpack_eq, le_iff_unpack_le]; exact UnpackedFloat.le_refl_iff

protected theorem not_le {a b : Float.Model} (ha : a ≠ nan) (hb : b ≠ nan) : ¬a ≤ b ↔ b < a := by
  rw [ne_eq, eq_nan_iff_unpack_eq] at ha hb
  exact UnpackedFloat.not_le ha hb

@[simp] theorem not_nan_lt (a : Float.Model) : ¬nan < a := by
  simp [lt_iff_unpack_lt, eq_nan_iff_unpack_eq.mp rfl]

@[simp] theorem not_lt_nan (a : Float.Model) : ¬a < nan := by
  simp [lt_iff_unpack_lt, eq_nan_iff_unpack_eq.mp rfl]

@[simp] theorem not_nan_le (a : Float.Model) : ¬nan ≤ a := by
  simp [le_iff_unpack_le, eq_nan_iff_unpack_eq.mp rfl]

@[simp] theorem not_le_nan (a : Float.Model) : ¬a ≤ nan := by
  simp [le_iff_unpack_le, eq_nan_iff_unpack_eq.mp rfl]

@[simp] theorem neg_lt_neg_iff {a b : Float.Model} : -a < -b ↔ b < a := by
  simp only [lt_iff_unpack_lt, unpack_neg, UnpackedFloat.neg_lt_neg]

@[simp] theorem neg_le_neg_iff {a b : Float.Model} : -a ≤ -b ↔ b ≤ a := by
  simp only [le_iff_unpack_le, unpack_neg, UnpackedFloat.neg_le_neg]

theorem minimum_comm (a b : Float.Model) : a.minimum b = b.minimum a := by
  simp only [minimum, UnpackedFloat.minimum_comm]

theorem maximum_comm (a b : Float.Model) : a.maximum b = b.maximum a := by
  simp only [maximum, UnpackedFloat.maximum_comm]

end Float.Model

namespace Float

@[simp] theorem toModel_nan : nan.toModel = .nan := rfl

@[simp] theorem toModel_neg (x : Float) : (-x).toModel = -x.toModel := rfl

theorem lt_iff_toModel_lt {x y : Float} : x < y ↔ x.toModel < y.toModel := by
  change Float.lt x y = true ↔ _
  simp [Float.lt]

theorem le_iff_toModel_le {x y : Float} : x ≤ y ↔ x.toModel ≤ y.toModel := by
  change Float.le x y = true ↔ _
  simp [Float.le]

theorem eq_nan_iff_toModel_eq {x : Float} : x = nan ↔ x.toModel = .nan := by
  cases x; simp [nan]

protected theorem lt_irrefl (x : Float) : ¬x < x := by
  simpa [lt_iff_toModel_lt] using Model.lt_irrefl x.toModel

protected theorem lt_asymm {x y : Float} : x < y → ¬y < x := by
  simpa [lt_iff_toModel_lt] using @Model.lt_asymm x.toModel y.toModel

protected theorem lt_trans {x y z : Float} : x < y → y < z → x < z := by
  simpa [lt_iff_toModel_lt] using @Model.lt_trans x.toModel y.toModel z.toModel

protected theorem le_trans {x y z : Float} : x ≤ y → y ≤ z → x ≤ z := by
  simpa [le_iff_toModel_le] using @Model.le_trans x.toModel y.toModel z.toModel

protected theorem lt_of_lt_of_le {x y z : Float} : x < y → y ≤ z → x < z := by
  simpa [lt_iff_toModel_lt, le_iff_toModel_le] using
    @Model.lt_of_lt_of_le x.toModel y.toModel z.toModel

protected theorem lt_of_le_of_lt {x y z : Float} : x ≤ y → y < z → x < z := by
  simpa [lt_iff_toModel_lt, le_iff_toModel_le] using
    @Model.lt_of_le_of_lt x.toModel y.toModel z.toModel

protected theorem le_of_lt {x y : Float} : x < y → x ≤ y := by
  simpa [lt_iff_toModel_lt, le_iff_toModel_le] using @Model.le_of_lt x.toModel y.toModel

protected theorem lt_iff_le_not_ge {x y : Float} : x < y ↔ x ≤ y ∧ ¬y ≤ x := by
  simpa [lt_iff_toModel_lt, le_iff_toModel_le] using @Model.lt_iff_le_not_ge x.toModel y.toModel

theorem le_refl_iff {x : Float} : x ≤ x ↔ x ≠ nan := by
  simpa [le_iff_toModel_le, eq_nan_iff_toModel_eq] using @Model.le_refl_iff x.toModel

protected theorem not_le {x y : Float} (hx : x ≠ nan) (hy : y ≠ nan) : ¬x ≤ y ↔ y < x := by
  rw [ne_eq, eq_nan_iff_toModel_eq] at hx hy
  simpa [lt_iff_toModel_lt, le_iff_toModel_le] using Model.not_le hx hy

@[simp] theorem not_nan_lt (x : Float) : ¬nan < x := by
  simp [lt_iff_toModel_lt]

@[simp] theorem not_lt_nan (x : Float) : ¬x < nan := by
  simp [lt_iff_toModel_lt]

@[simp] theorem not_nan_le (x : Float) : ¬nan ≤ x := by
  simp [le_iff_toModel_le]

@[simp] theorem not_le_nan (x : Float) : ¬x ≤ nan := by
  simp [le_iff_toModel_le]

@[simp] theorem neg_lt_neg_iff {x y : Float} : -x < -y ↔ y < x := by
  simp [lt_iff_toModel_lt]

@[simp] theorem neg_le_neg_iff {x y : Float} : -x ≤ -y ↔ y ≤ x := by
  simp [le_iff_toModel_le]

protected theorem min_comm (x y : Float) : min x y = min y x := by
  change ofModel (x.toModel.minimum y.toModel) = ofModel (y.toModel.minimum x.toModel)
  rw [Model.minimum_comm]

protected theorem max_comm (x y : Float) : max x y = max y x := by
  change ofModel (x.toModel.maximum y.toModel) = ofModel (y.toModel.maximum x.toModel)
  rw [Model.maximum_comm]

end Float

namespace Float32.Model

open Float.Model

theorem lt_iff_unpack_lt {a b : Float32.Model} : a < b ↔ a.unpack.lt b.unpack := Iff.rfl

theorem le_iff_unpack_le {a b : Float32.Model} : a ≤ b ↔ a.unpack.le b.unpack := Iff.rfl

theorem eq_nan_iff_unpack_eq {a : Float32.Model} : a = nan ↔ a.unpack = .notANumber := by
  constructor
  · rintro rfl; simp [nan, unpack, pack, UnpackedFloat.pack]
  · intro h; rw [← pack_unpack a, h]; rfl

theorem unpack_neg (a : Float32.Model) : (-a).unpack = a.unpack.neg := unpack_pack_neg_unpack a

protected theorem lt_irrefl (a : Float32.Model) : ¬a < a := UnpackedFloat.lt_irrefl _

protected theorem lt_asymm {a b : Float32.Model} : a < b → ¬b < a := UnpackedFloat.lt_asymm

protected theorem lt_trans {a b c : Float32.Model} : a < b → b < c → a < c := UnpackedFloat.lt_trans

protected theorem le_trans {a b c : Float32.Model} : a ≤ b → b ≤ c → a ≤ c := UnpackedFloat.le_trans

protected theorem lt_of_lt_of_le {a b c : Float32.Model} : a < b → b ≤ c → a < c :=
  UnpackedFloat.lt_of_lt_of_le

protected theorem lt_of_le_of_lt {a b c : Float32.Model} : a ≤ b → b < c → a < c :=
  UnpackedFloat.lt_of_le_of_lt

protected theorem le_of_lt {a b : Float32.Model} : a < b → a ≤ b := UnpackedFloat.le_of_lt

protected theorem lt_iff_le_not_ge {a b : Float32.Model} : a < b ↔ a ≤ b ∧ ¬b ≤ a :=
  UnpackedFloat.lt_iff_le_not_ge

theorem le_refl_iff {a : Float32.Model} : a ≤ a ↔ a ≠ nan := by
  rw [ne_eq, eq_nan_iff_unpack_eq, le_iff_unpack_le]; exact UnpackedFloat.le_refl_iff

protected theorem not_le {a b : Float32.Model} (ha : a ≠ nan) (hb : b ≠ nan) : ¬a ≤ b ↔ b < a := by
  rw [ne_eq, eq_nan_iff_unpack_eq] at ha hb
  exact UnpackedFloat.not_le ha hb

@[simp] theorem not_nan_lt (a : Float32.Model) : ¬nan < a := by
  simp [lt_iff_unpack_lt, eq_nan_iff_unpack_eq.mp rfl]

@[simp] theorem not_lt_nan (a : Float32.Model) : ¬a < nan := by
  simp [lt_iff_unpack_lt, eq_nan_iff_unpack_eq.mp rfl]

@[simp] theorem not_nan_le (a : Float32.Model) : ¬nan ≤ a := by
  simp [le_iff_unpack_le, eq_nan_iff_unpack_eq.mp rfl]

@[simp] theorem not_le_nan (a : Float32.Model) : ¬a ≤ nan := by
  simp [le_iff_unpack_le, eq_nan_iff_unpack_eq.mp rfl]

@[simp] theorem neg_lt_neg_iff {a b : Float32.Model} : -a < -b ↔ b < a := by
  simp only [lt_iff_unpack_lt, unpack_neg, UnpackedFloat.neg_lt_neg]

@[simp] theorem neg_le_neg_iff {a b : Float32.Model} : -a ≤ -b ↔ b ≤ a := by
  simp only [le_iff_unpack_le, unpack_neg, UnpackedFloat.neg_le_neg]

theorem minimum_comm (a b : Float32.Model) : a.minimum b = b.minimum a := by
  simp only [minimum, UnpackedFloat.minimum_comm]

theorem maximum_comm (a b : Float32.Model) : a.maximum b = b.maximum a := by
  simp only [maximum, UnpackedFloat.maximum_comm]

end Float32.Model

namespace Float32

@[simp] theorem toModel_nan : nan.toModel = .nan := rfl

@[simp] theorem toModel_neg (x : Float32) : (-x).toModel = -x.toModel := rfl

theorem lt_iff_toModel_lt {x y : Float32} : x < y ↔ x.toModel < y.toModel := by
  change Float32.lt x y = true ↔ _
  simp [Float32.lt]

theorem le_iff_toModel_le {x y : Float32} : x ≤ y ↔ x.toModel ≤ y.toModel := by
  change Float32.le x y = true ↔ _
  simp [Float32.le]

theorem eq_nan_iff_toModel_eq {x : Float32} : x = nan ↔ x.toModel = .nan := by
  cases x; simp [nan]

protected theorem lt_irrefl (x : Float32) : ¬x < x := by
  simpa [lt_iff_toModel_lt] using Model.lt_irrefl x.toModel

protected theorem lt_asymm {x y : Float32} : x < y → ¬y < x := by
  simpa [lt_iff_toModel_lt] using @Model.lt_asymm x.toModel y.toModel

protected theorem lt_trans {x y z : Float32} : x < y → y < z → x < z := by
  simpa [lt_iff_toModel_lt] using @Model.lt_trans x.toModel y.toModel z.toModel

protected theorem le_trans {x y z : Float32} : x ≤ y → y ≤ z → x ≤ z := by
  simpa [le_iff_toModel_le] using @Model.le_trans x.toModel y.toModel z.toModel

protected theorem lt_of_lt_of_le {x y z : Float32} : x < y → y ≤ z → x < z := by
  simpa [lt_iff_toModel_lt, le_iff_toModel_le] using
    @Model.lt_of_lt_of_le x.toModel y.toModel z.toModel

protected theorem lt_of_le_of_lt {x y z : Float32} : x ≤ y → y < z → x < z := by
  simpa [lt_iff_toModel_lt, le_iff_toModel_le] using
    @Model.lt_of_le_of_lt x.toModel y.toModel z.toModel

protected theorem le_of_lt {x y : Float32} : x < y → x ≤ y := by
  simpa [lt_iff_toModel_lt, le_iff_toModel_le] using @Model.le_of_lt x.toModel y.toModel

protected theorem lt_iff_le_not_ge {x y : Float32} : x < y ↔ x ≤ y ∧ ¬y ≤ x := by
  simpa [lt_iff_toModel_lt, le_iff_toModel_le] using @Model.lt_iff_le_not_ge x.toModel y.toModel

theorem le_refl_iff {x : Float32} : x ≤ x ↔ x ≠ nan := by
  simpa [le_iff_toModel_le, eq_nan_iff_toModel_eq] using @Model.le_refl_iff x.toModel

protected theorem not_le {x y : Float32} (hx : x ≠ nan) (hy : y ≠ nan) : ¬x ≤ y ↔ y < x := by
  rw [ne_eq, eq_nan_iff_toModel_eq] at hx hy
  simpa [lt_iff_toModel_lt, le_iff_toModel_le] using Model.not_le hx hy

@[simp] theorem not_nan_lt (x : Float32) : ¬nan < x := by
  simp [lt_iff_toModel_lt]

@[simp] theorem not_lt_nan (x : Float32) : ¬x < nan := by
  simp [lt_iff_toModel_lt]

@[simp] theorem not_nan_le (x : Float32) : ¬nan ≤ x := by
  simp [le_iff_toModel_le]

@[simp] theorem not_le_nan (x : Float32) : ¬x ≤ nan := by
  simp [le_iff_toModel_le]

@[simp] theorem neg_lt_neg_iff {x y : Float32} : -x < -y ↔ y < x := by
  simp [lt_iff_toModel_lt]

@[simp] theorem neg_le_neg_iff {x y : Float32} : -x ≤ -y ↔ y ≤ x := by
  simp [le_iff_toModel_le]

protected theorem min_comm (x y : Float32) : min x y = min y x := by
  change ofModel (x.toModel.minimum y.toModel) = ofModel (y.toModel.minimum x.toModel)
  rw [Model.minimum_comm]

protected theorem max_comm (x y : Float32) : max x y = max y x := by
  change ofModel (x.toModel.maximum y.toModel) = ofModel (y.toModel.maximum x.toModel)
  rw [Model.maximum_comm]

end Float32
