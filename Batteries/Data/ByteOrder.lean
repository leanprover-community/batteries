/-
Copyright (c) 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: François G. Dorais
-/

module
import Batteries.Util.ProofWanted
meta import Std.Tactic.BVDecide
import Std.Tactic.BVDecide.Bitblast.BVExpr.Basic
public import Batteries.Data.ByteArray

/-! # Byte Order

Basic utilities to handle byte order for scalar types.
-/

set_option linter.missingDocs false in
/-- Byte ordering for scalar types.

* `platform`: byte ordering of the host platform
* `bigEndian`: scalar types are stored most significant byte first
* `littleEndian`: scalar types are stored least significant byte first

The host platform is expected to be either big endian or little endian. There are rare platforms
that are mixed endian; these platforms are not well supported.
-/
public inductive System.ByteOrder
| public platform
| public bigEndian
| public littleEndian
deriving Inhabited, DecidableEq, Repr
attribute [inherit_doc System.ByteOrder] System.ByteOrder.platform
attribute [inherit_doc System.ByteOrder] System.ByteOrder.bigEndian
attribute [inherit_doc System.ByteOrder] System.ByteOrder.littleEndian

/-- Determine the byte order of the host platform.

The host platform is expected to be `bigEndian` or `littleEndian`. In the rare
event that the platform is mixed endian, `System.byteOrder.platform` is returned.
-/
public def System.Platform.byteOrder : System.ByteOrder :=
  if ntohl 0x01020304 = 0x01020304 then
    .bigEndian
  else if ntohl 0x01020304 = 0x04030201 then
    .littleEndian
  else
    .platform
  where
    /-- The C function `ntohl` converts a `UInt32` in network byte order (big endian) to a
      `UInt32` in host byte order. -/
    @[extern "ntohl"] ntohl : UInt32 → UInt32 := id

/-- Swap the bytes of a `UInt16` scalar. -/
@[expose, inline]
public def UInt16.byteswap (x : UInt16) : UInt16 :=
  x <<< 8 ||| x >>> 8

@[simp, grind =]
theorem UInt16.byteswap_byteswap (x : UInt16) : x.byteswap.byteswap = x := by
  simp only [byteswap]
  bv_decide

/-- Swap the bytes of a `UInt32` scalar. -/
@[expose, inline]
public def UInt32.byteswap (x : UInt32) : UInt32 :=
  let x := x <<< 16 ||| x >>> 16
  (x &&& 0xFF00FF00) >>> 8 ||| (x <<< 8 &&& 0xFF00FF00)

@[simp, grind =]
theorem UInt32.byteswap_byteswap (x : UInt32) : x.byteswap.byteswap = x := by
  simp only [byteswap]
  bv_decide

/-- Swap the byte of a `UInt64` scalar. -/
@[expose, inline]
public def UInt64.byteswap (x : UInt64) : UInt64 :=
  let x := x <<< 32 ||| x >>> 32
  let x := (x &&& 0xFFFF0000FFFF0000) >>> 16 ||| (x <<< 16 &&& 0xFFFF0000FFFF0000)
  (x &&& 0xFF00FF00FF00FF00) >>> 8 ||| (x <<< 8 &&& 0xFF00FF00FF00FF00)

@[simp, grind =]
theorem UInt64.byteswap_byteswap (x : UInt64) : x.byteswap.byteswap = x := by
  simp only [byteswap]
  bv_decide

/-- Convert to `endian` byte ordering. -/
@[expose, inline]
public def UInt16.toByteOrder (x : UInt16) (endian : System.ByteOrder) : UInt16 :=
  match endian, System.Platform.byteOrder with
  | .littleEndian, .bigEndian | .bigEndian, .littleEndian => x.byteswap
  | _, _ => x

/-- Convert to big endian byte ordering. -/
public abbrev UInt16.toBigEndian (x : UInt16) : UInt16 := x.toByteOrder .bigEndian

/-- Convert to little endian byte ordering. -/
public abbrev UInt16.toLittleEndian (x : UInt16) : UInt16 := x.toByteOrder .littleEndian

/-- Convert to `endian` byte ordering. -/
@[expose, inline]
public def UInt32.toByteOrder (x : UInt32) (endian : System.ByteOrder) : UInt32 :=
  match endian, System.Platform.byteOrder with
  | .littleEndian, .bigEndian | .bigEndian, .littleEndian => x.byteswap
  | _, _ => x

/-- Convert to big endian byte ordering. -/
public abbrev UInt32.toBigEndian (x : UInt32) : UInt32 := x.toByteOrder .bigEndian

/-- Convert to little endian byte ordering. -/
public abbrev UInt32.toLittleEndian (x : UInt32) : UInt32 := x.toByteOrder .littleEndian

/-- Convert to `endian` byte ordering. -/
@[expose, inline]
public def UInt64.toByteOrder (x : UInt64) (endian : System.ByteOrder) : UInt64 :=
  match endian, System.Platform.byteOrder with
  | .littleEndian, .bigEndian | .bigEndian, .littleEndian => x.byteswap
  | _, _ => x

/-- Convert to big endian byte ordering. -/
public abbrev UInt64.toBigEndian (x : UInt64) : UInt64 := x.toByteOrder .bigEndian

/-- Convert to little endian byte ordering. -/
public abbrev UInt64.toLittleEndian (x : UInt64) : UInt64 := x.toByteOrder .littleEndian

/-- Convert a byte array of size 2 into a `UInt16` scalar in platform byte order. -/
@[expose, never_extract, extern c inline "*(uint16_t*)lean_sarray_cptr(#1)"]
public def UInt16.ofByteArray (b : @& ByteArray) (h : b.size = 2) : UInt16 :=
  if System.Platform.byteOrder = .littleEndian then
    b[1].toUInt16 <<< 8 ||| b[0].toUInt16
  else -- default to big endian even if platform is mixed endian
    b[0].toUInt16 <<< 8 ||| b[1].toUInt16

/-- Convert a byte array of size 4 into a `UInt32` scalar in platform byte order. -/
@[expose, never_extract, extern c inline "*(uint32_t*)lean_sarray_cptr(#1)"]
public def UInt32.ofByteArray (b : @& ByteArray) (h : b.size = 4) : UInt32 :=
  if System.Platform.byteOrder = .littleEndian then
    ((b[3].toUInt32 <<< 8 ||| b[2].toUInt32) <<< 8 ||| b[1].toUInt32) <<< 8 ||| b[0].toUInt32
  else -- default to big endian even if platform is mixed endian
    ((b[0].toUInt32 <<< 8 ||| b[1].toUInt32) <<< 8 ||| b[2].toUInt32) <<< 8 ||| b[3].toUInt32

/-- Convert a byte array of size 8 into a `UInt64` scalar in platform byte order. -/
@[expose, never_extract, extern c inline "*(uint64_t*)lean_sarray_cptr(#1)"]
public def UInt64.ofByteArray (b : @& ByteArray) (h : b.size = 8) : UInt64 :=
  if System.Platform.byteOrder = .littleEndian then
    ((((((b[7].toUInt64 <<< 8 ||| b[6].toUInt64) <<< 8
      ||| b[5].toUInt64) <<< 8 ||| b[4].toUInt64) <<< 8
      ||| b[3].toUInt64) <<< 8 ||| b[2].toUInt64) <<< 8
      ||| b[1].toUInt64) <<< 8 ||| b[0].toUInt64
  else -- default to big endian even if platform is mixed endian
    ((((((b[0].toUInt64 <<< 8 ||| b[1].toUInt64) <<< 8
      ||| b[2].toUInt64) <<< 8 ||| b[3].toUInt64) <<< 8
      ||| b[4].toUInt64) <<< 8 ||| b[5].toUInt64) <<< 8
      ||| b[6].toUInt64) <<< 8 ||| b[7].toUInt64

@[inline]
unsafe def UInt16.toByteArrayImpl (x : UInt16) : ByteArray :=
  set (ByteArray.allocate 2 2 (USize.le_refl _)) x
where
  @[extern c inline "#1;\n*(uint16_t*)lean_sarray_cptr(#1) = #2"]
  set (_b : ByteArray) (_x : UInt16) := _b

/-- Convert a `UInt16` scalar into a byte array in platform byte order. -/
@[expose, implemented_by UInt16.toByteArrayImpl]
public def UInt16.toByteArray (x : UInt16) : ByteArray :=
  if System.Platform.byteOrder = .littleEndian then
    .mk #[x.toUInt8, (x >>> 8).toUInt8]
  else -- default to big endian even if platform is mixed endian
    .mk #[(x >>> 8).toUInt8, x.toUInt8]

@[simp, grind =]
public theorem UInt16.size_toByteArray {x : UInt16} : x.toByteArray.size = 2 := by
  cases _ : System.Platform.byteOrder <;> (simp only [toByteArray, *]; rfl)

@[grind =]
public theorem UInt16.getElem_toByteArray_littleEndian
    (h : System.Platform.byteOrder = .littleEndian) (x : UInt16) (i) (hi : i < x.toByteArray.size) :
    x.toByteArray[i] = (x >>> (8 * i.toUInt16)).toUInt8 := by
  simp only [toByteArray, h, ↓reduceIte, ByteArray.getElem_eq_data_getElem, List.getElem_toArray,
    Nat.toUInt16_eq]
  match i with | 0 | 1 => rfl

@[grind =]
public theorem UInt16.getElem_toByteArray_bigEndian (h : System.Platform.byteOrder = .bigEndian)
    (x : UInt16) (i) (hi : i < x.toByteArray.size) :
    x.toByteArray[i] = (x >>> (8 * (1 - i).toUInt16)).toUInt8 := by
  simp only [toByteArray, h, reduceCtorEq, ↓reduceIte, ByteArray.getElem_eq_data_getElem,
    List.getElem_toArray, Nat.toUInt16_eq]
  match i with | 0 | 1 => simp

@[inline]
unsafe def UInt32.toByteArrayImpl (x : UInt32) : ByteArray :=
  set (ByteArray.allocate 4 4 (USize.le_refl _)) x
where
  @[extern c inline "#1;\n*(uint32_t*)lean_sarray_cptr(#1) = #2"]
  set (_b : ByteArray) (_x : UInt32) := _b

/-- Convert a `UInt32` scalar into a byte array in platform byte order. -/
@[expose, implemented_by UInt32.toByteArrayImpl]
public def UInt32.toByteArray (x : UInt32) : ByteArray :=
  if System.Platform.byteOrder = .littleEndian then
    .mk #[x.toUInt8, (x >>> 8).toUInt8, (x >>> 16).toUInt8, (x >>> 24).toUInt8]
  else -- default to big endian even if platform is mixed endian
    .mk #[(x >>> 24).toUInt8, (x >>> 16).toUInt8, (x >>> 8).toUInt8, x.toUInt8]

@[simp, grind =]
public theorem UInt32.size_toByteArray {x : UInt32} : x.toByteArray.size = 4 := by
  cases _ : System.Platform.byteOrder <;> (simp only [toByteArray, *]; rfl)

@[grind =]
public theorem UInt32.getElem_toByteArray_littleEndian
    (h : System.Platform.byteOrder = .littleEndian) (x : UInt32) (i) (hi : i < x.toByteArray.size) :
    x.toByteArray[i] = (x >>> (8 * i.toUInt32)).toUInt8 := by
  simp only [toByteArray, h, ↓reduceIte, ByteArray.getElem_eq_data_getElem, List.getElem_toArray,
    Nat.toUInt32_eq]
  match i with | 0 | 1 | 2 | 3 => rfl

@[grind =]
public theorem UInt32.getElem_toByteArray_bigEndian (h : System.Platform.byteOrder = .bigEndian)
    (x : UInt32) (i) (hi : i < x.toByteArray.size) :
    x.toByteArray[i] = (x >>> (8 * (3 - i).toUInt32)).toUInt8 := by
  simp only [toByteArray, h, reduceCtorEq, ↓reduceIte, ByteArray.getElem_eq_data_getElem,
    List.getElem_toArray, Nat.toUInt32_eq]
  match i with | 0 | 1 | 2 | 3 => simp

@[inline]
unsafe def UInt64.toByteArrayImpl (x : UInt64) : ByteArray :=
  set (ByteArray.allocate 8 8 (USize.le_refl _)) x
where
  @[extern c inline "#1;\n*(uint64_t*)lean_sarray_cptr(#1) = #2"]
  set (_b : ByteArray) (_x : UInt64) := _b

/-- Convert a `UInt64` scalar into a byte array in platform byte order. -/
@[expose, implemented_by UInt64.toByteArrayImpl]
public def UInt64.toByteArray (x : UInt64) : ByteArray :=
  if System.Platform.byteOrder = .littleEndian then
    .mk #[x.toUInt8, (x >>> 8).toUInt8, (x >>> 16).toUInt8, (x >>> 24).toUInt8,
      (x >>> 32).toUInt8, (x >>> 40).toUInt8, (x >>> 48).toUInt8, (x >>> 56).toUInt8]
  else -- default to big endian even if platform is mixed endian
    .mk #[(x >>> 56).toUInt8, (x >>> 48).toUInt8, (x >>> 40).toUInt8, (x >>> 32).toUInt8,
      (x >>> 24).toUInt8, (x >>> 16).toUInt8, (x >>> 8).toUInt8, x.toUInt8]

@[grind =]
public theorem UInt64.getElem_toByteArray_littleEndian (h : System.Platform.byteOrder = .littleEndian)
    (x : UInt64) (i) (hi : i < x.toByteArray.size) :
    x.toByteArray[i] = (x >>> (8 * i.toUInt64)).toUInt8 := by
  simp only [toByteArray, h, ↓reduceIte, ByteArray.getElem_eq_data_getElem, List.getElem_toArray,
    Nat.toUInt64_eq]
  match i with | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 => rfl

@[grind =]
public theorem UInt64.getElem_toByteArray_bigEndian (h : System.Platform.byteOrder = .bigEndian)
    (x : UInt64) (i) (hi : i < x.toByteArray.size) :
    x.toByteArray[i] = (x >>> (8 * (7 - i).toUInt64)).toUInt8 := by
  simp only [toByteArray, h, reduceCtorEq, ↓reduceIte, ByteArray.getElem_eq_data_getElem,
    List.getElem_toArray, Nat.toUInt64_eq]
  match i with | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 => simp

@[simp, grind =]
public theorem UInt64.size_toByteArray {x : UInt64} : x.toByteArray.size = 8 := by
  cases _ : System.Platform.byteOrder <;> (simp only [toByteArray, *]; rfl)

@[simp, grind =]
public theorem UInt16.ofByteArray_toByteArray (x : UInt16) :
    ofByteArray x.toByteArray size_toByteArray = x := by
  cases hp : System.Platform.byteOrder <;> simp only [ofByteArray, hp, reduceCtorEq, ↓reduceIte,
    toByteArray, ByteArray.getElem_eq_data_getElem, List.getElem_toArray, List.getElem_cons_zero,
    toUInt16_toUInt8, List.getElem_cons_succ]
  all_goals bv_decide

@[simp, grind =]
public theorem UInt32.ofByteArray_toByteArray (x : UInt32) :
    ofByteArray x.toByteArray size_toByteArray = x := by
  cases hp : System.Platform.byteOrder <;> simp only [ofByteArray, hp, reduceCtorEq, ↓reduceIte,
    toByteArray, ByteArray.getElem_eq_data_getElem, List.getElem_toArray, List.getElem_cons_zero,
    toUInt32_toUInt8, List.getElem_cons_succ]
  all_goals bv_decide

@[simp, grind =]
public theorem UInt64.ofByteArray_toByteArray (x : UInt64) :
    ofByteArray x.toByteArray size_toByteArray = x := by
  cases h : System.Platform.byteOrder <;> simp only [ofByteArray, h, reduceCtorEq, ↓reduceIte,
    toByteArray, ByteArray.getElem_eq_data_getElem, List.getElem_toArray, List.getElem_cons_zero,
    toUInt64_toUInt8, List.getElem_cons_succ]
  all_goals bv_decide

proof_wanted UInt16.toByteArray_ofByteArray (b : ByteArray) (h : b.size = 2) :
    (ofByteArray b h).toByteArray = b

proof_wanted UInt32.toByteArray_ofByteArray (b : ByteArray) (h : b.size = 4) :
    (ofByteArray b h).toByteArray = b

proof_wanted UInt64.toByteArray_ofByteArray (b : ByteArray) (h : b.size = 8) :
    (ofByteArray b h).toByteArray = b
