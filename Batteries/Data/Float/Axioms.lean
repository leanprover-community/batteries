/-
Copyright (c) 2025 Robin Arnez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robin Arnez
-/

import Batteries.Data.Float.Basic
import Lean.Elab.Tactic

/-!
# Axiomatic redefinition of float functions

In this file, the most common floating point functions are
axiomatically redefined to be used to later prove theorems about them.
This is a temporary file, once there actually is a definition in
core Lean, this will become unnecessary.
-/

-- we don't want 10 different axioms for floats, we combine them here into one
private structure Float.AxiomSet where
  ofBits_toBits (x : Float) : ofBits x.toBits = x
  toBits_ofBits (x : UInt64) : (ofBits x).toBits = if isNaNBits x then 0x7ff8_0000_0000_0000 else x
  isNaN_def (x : Float) : x.isNaN = isNaNBits x.toBits
  isInf_def (x : Float) : x.isInf = (x.exponentPart = 2047 ∧ x.mantissa = 0)
  isFinite_def (x : Float) : x.isFinite = (x.exponentPart < 2047)
  neg_def (x : Float) : x.neg = ofBits (x.toBits ^^^ 0x8000_0000_0000_0000)

/--
Auxiliary axiom redefining the opaque `Float` functions.
-/
axiom Float.definitionAxiom : Float.AxiomSet

theorem Float.ofBits_toBits (x : Float) : ofBits x.toBits = x :=
  Float.definitionAxiom.ofBits_toBits x

theorem Float.toBits_ofBits (x : UInt64) :
    (ofBits x).toBits = if isNaNBits x then 0x7ff8_0000_0000_0000 else x :=
  Float.definitionAxiom.toBits_ofBits x

theorem Float.isNaN.eq_def (x : Float) :
    x.isNaN = Float.isNaNBits x.toBits :=
  Float.definitionAxiom.isNaN_def x

theorem Float.isNaN.eq_1 (x : Float) :
    x.isNaN = Float.isNaNBits x.toBits := by
  unfold Float.isNaN; rfl

theorem Float.isInf.eq_def (x : Float) :
    x.isInf = (x.exponentPart = 2047 ∧ x.mantissa = 0) :=
  Float.definitionAxiom.isInf_def x

theorem Float.isInf.eq_1 (x : Float) :
    x.isInf = (x.exponentPart = 2047 ∧ x.mantissa = 0) := by
  unfold Float.isInf; rfl

theorem Float.isFinite.eq_def (x : Float) :
    x.isFinite = (x.exponentPart < 2047) :=
  Float.definitionAxiom.isFinite_def x

theorem Float.isFinite.eq_1 (x : Float) :
    x.isFinite = (x.exponentPart < 2047) := by
  unfold Float.isFinite; rfl

theorem Float.neg.eq_def (x : Float) :
    x.neg = ofBits (x.toBits ^^^ 0x8000_0000_0000_0000) :=
  Float.definitionAxiom.neg_def x

theorem Float.neg.eq_1 (x : Float) :
    x.neg = ofBits (x.toBits ^^^ 0x8000_0000_0000_0000) := by
  unfold Float.neg; rfl
