/-
 Copyright (c) 2026 François G. Dorais. All rights reserved.
 Released under Apache 2.0 license as described in the file LICENSE.
 Authors: François G. Dorais
-/
module

public import Batteries.Data.Float.Lemmas

/-!
# Total order on `Float` and `Float32`

The IEEE 754 comparisons `<`, `≤` and `==` on floating-point numbers are not a total order:
`NaN` is incomparable with everything, and `-0 == 0`. This file provides the `totalOrder`
predicate of IEEE 754-2019 §5.10 as a lawful comparison function `Float.totalCmp`, and wrapper
types `TotalFloat` and `TotalFloat32` whose `Ord`, `BEq`, `Hashable` and `DecidableEq` instances
all agree with it, so that floating-point numbers can be used as keys in ordered and hashed
containers.

The order is `-inf < … < -0 < 0 < … < inf < nan`. Since Lean's floats have a single `NaN` value, it is the
largest element, as `+NaN` is in IEEE 754-2019. This matches Julia's `isless`, and Rust's
`total_cmp` on non-negative `NaN`s.
-/

namespace Float

/-- The bit-level map behind `totalOrderKey`. -/
@[expose] public def totalOrderKeyOfBits (b : UInt64) : UInt64 :=
  if b < 0x8000000000000000 then b + 0x8000000000000000 else ~~~b

public theorem totalOrderKeyOfBits_inj {b c : UInt64} :
    totalOrderKeyOfBits b = totalOrderKeyOfBits c ↔ b = c := by
  refine ⟨fun h => ?_, (· ▸ rfl)⟩
  have := b.toNat_lt_size
  have := c.toNat_lt_size
  unfold totalOrderKeyOfBits at h
  split at h <;> split at h <;>
    simp only [← UInt64.toNat_inj, UInt64.toNat_add, UInt64.toNat_not, UInt64.lt_iff_toNat_lt,
      UInt64.reduceToNat, UInt64.size] at * <;> lia

/--
The key that sorts `Float` values according to `totalCmp`: negative numbers have their bits
flipped and non-negative numbers have their sign bit set, so that unsigned comparison of keys
is the IEEE 754-2019 `totalOrder`.
-/
@[expose] public def totalOrderKey (x : Float) : UInt64 :=
  -- Use the canonical `NaN` so that compiled code agrees with the model for any `NaN` bits.
  totalOrderKeyOfBits (if x.isNaN then nan.toBits else x.toBits)

/--
The IEEE 754-2019 `totalOrder` comparison: `-inf < … < -0 < 0 < … < inf < nan`.

Unlike `compare` on floats via `<` and `==`, this is a lawful total order: it distinguishes `-0`
from `0` and places `NaN` above every other value.
-/
@[expose] public def totalCmp (x y : Float) : Ordering :=
  compareOn totalOrderKey x y

public theorem totalOrderKey_inj {x y : Float} :
    x.totalOrderKey = y.totalOrderKey ↔ x = y := by
  have key (x : Float) : (if x.isNaN then nan.toBits else x.toBits) = x.toBits := by
    split <;> simp_all [Float.isNaN_eq_decide_eq_nan]
  simp only [totalOrderKey, key, totalOrderKeyOfBits_inj, Float.toBits_inj]

public instance : Std.TransCmp totalCmp :=
  inferInstanceAs (Std.TransCmp (compareOn totalOrderKey))

public instance : Std.LawfulEqCmp totalCmp where
  eq_of_compare h := totalOrderKey_inj.mp (Std.LawfulEqOrd.eq_of_compare (α := UInt64) h)

end Float

namespace Float32

/-- The bit-level map behind `totalOrderKey`. -/
@[expose] public def totalOrderKeyOfBits (b : UInt32) : UInt32 :=
  if b < 0x80000000 then b + 0x80000000 else ~~~b

public theorem totalOrderKeyOfBits_inj {b c : UInt32} :
    totalOrderKeyOfBits b = totalOrderKeyOfBits c ↔ b = c := by
  refine ⟨fun h => ?_, (· ▸ rfl)⟩
  have := b.toNat_lt_size
  have := c.toNat_lt_size
  unfold totalOrderKeyOfBits at h
  split at h <;> split at h <;>
    simp only [← UInt32.toNat_inj, UInt32.toNat_add, UInt32.toNat_not, UInt32.lt_iff_toNat_lt,
      UInt32.reduceToNat, UInt32.size] at * <;> lia

@[inherit_doc Float.totalOrderKey, expose]
public def totalOrderKey (x : Float32) : UInt32 :=
  -- Use the canonical `NaN` so that compiled code agrees with the model for any `NaN` bits.
  totalOrderKeyOfBits (if x.isNaN then nan.toBits else x.toBits)

@[inherit_doc Float.totalCmp, expose]
public def totalCmp (x y : Float32) : Ordering :=
  compareOn totalOrderKey x y

public theorem totalOrderKey_inj {x y : Float32} :
    x.totalOrderKey = y.totalOrderKey ↔ x = y := by
  have key (x : Float32) : (if x.isNaN then nan.toBits else x.toBits) = x.toBits := by
    split <;> simp_all [Float32.isNaN_eq_decide_eq_nan]
  simp only [totalOrderKey, key, totalOrderKeyOfBits_inj, Float32.toBits_inj]

public instance : Std.TransCmp totalCmp :=
  inferInstanceAs (Std.TransCmp (compareOn totalOrderKey))

public instance : Std.LawfulEqCmp totalCmp where
  eq_of_compare h := totalOrderKey_inj.mp (Std.LawfulEqOrd.eq_of_compare (α := UInt32) h)

end Float32

/--
A `Float` ordered by the IEEE 754-2019 `totalOrder` (`Float.totalCmp`), for use as a key in
ordered and hashed containers. Its `Ord`, `BEq`, `Hashable` and `DecidableEq` instances agree:
`-0` and `0` are distinct, and `NaN` equals itself and is the largest value.
-/
public structure TotalFloat where
  /-- The underlying `Float`. -/
  val : Float
deriving DecidableEq, Inhabited

namespace TotalFloat

public instance : Coe Float TotalFloat := ⟨mk⟩

public instance : Ord TotalFloat := ⟨fun x y => x.val.totalCmp y.val⟩

public instance : BEq TotalFloat := ⟨fun x y => x.val.totalOrderKey == y.val.totalOrderKey⟩

public instance : Hashable TotalFloat := ⟨fun x => hash x.val.totalOrderKey⟩

public instance : LT TotalFloat := ltOfOrd
public instance : LE TotalFloat := leOfOrd

public instance : Std.TransOrd TotalFloat :=
  inferInstanceAs (Std.TransCmp (compareOn fun x : TotalFloat => x.val.totalOrderKey))

public instance : Std.LawfulEqOrd TotalFloat where
  eq_of_compare h := congrArg mk (Std.LawfulEqCmp.eq_of_compare (cmp := Float.totalCmp) h)

public instance : LawfulBEq TotalFloat where
  rfl {x} := beq_self_eq_true (α := UInt64) x.val.totalOrderKey
  eq_of_beq h := congrArg mk (Float.totalOrderKey_inj.mp (eq_of_beq (α := UInt64) h))

public instance : LawfulHashable TotalFloat where
  hash_eq _ _ h := congrArg (hash : UInt64 → UInt64) (eq_of_beq (α := UInt64) h)

public instance : Repr TotalFloat := ⟨fun x p => reprPrec x.val p⟩
public instance : ToString TotalFloat := ⟨fun x => toString x.val⟩

end TotalFloat

/--
A `Float32` ordered by the IEEE 754-2019 `totalOrder` (`Float32.totalCmp`), for use as a key in
ordered and hashed containers. Its `Ord`, `BEq`, `Hashable` and `DecidableEq` instances agree:
`-0` and `0` are distinct, and `NaN` equals itself and is the largest value.
-/
public structure TotalFloat32 where
  /-- The underlying `Float32`. -/
  val : Float32
deriving DecidableEq, Inhabited

namespace TotalFloat32

public instance : Coe Float32 TotalFloat32 := ⟨mk⟩

public instance : Ord TotalFloat32 := ⟨fun x y => x.val.totalCmp y.val⟩

public instance : BEq TotalFloat32 := ⟨fun x y => x.val.totalOrderKey == y.val.totalOrderKey⟩

public instance : Hashable TotalFloat32 := ⟨fun x => hash x.val.totalOrderKey⟩

public instance : LT TotalFloat32 := ltOfOrd
public instance : LE TotalFloat32 := leOfOrd

public instance : Std.TransOrd TotalFloat32 :=
  inferInstanceAs (Std.TransCmp (compareOn fun x : TotalFloat32 => x.val.totalOrderKey))

public instance : Std.LawfulEqOrd TotalFloat32 where
  eq_of_compare h := congrArg mk (Std.LawfulEqCmp.eq_of_compare (cmp := Float32.totalCmp) h)

public instance : LawfulBEq TotalFloat32 where
  rfl {x} := beq_self_eq_true (α := UInt32) x.val.totalOrderKey
  eq_of_beq h := congrArg mk (Float32.totalOrderKey_inj.mp (eq_of_beq (α := UInt32) h))

public instance : LawfulHashable TotalFloat32 where
  hash_eq _ _ h := congrArg (hash : UInt32 → UInt64) (eq_of_beq (α := UInt32) h)

public instance : Repr TotalFloat32 := ⟨fun x p => reprPrec x.val p⟩
public instance : ToString TotalFloat32 := ⟨fun x => toString x.val⟩

end TotalFloat32
