/-
Copyright (c) 2024 Shreyas Srinivas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shreyas Srinivas, Francois Dorais
-/

import Batteries.Data.Vector.Basic

/-!
## Vector.Unexpanders

The definitions in this file are used to provide unexpanders in metaprogramming.
They correspond to similar array definitions `mkArray0`,...,`mkArray8` and their unexpanders
-/

namespace Vector

/-- Create empty vector `#v[]`-/
def mkVector0 : Vector α 0 := empty

/-- Create vector `#v[v₁]` -/
def mkVector1 (v₁ : α) : Vector α 1 :=
  mkEmpty 1 |> push v₁

/-- Create vector `#v[v₁, v₂]` -/
def mkVector2 (v₁ v₂ : α) : Vector α 2 :=
  mkEmpty 2
    |> push v₁
    |> push v₂

/-- Create vector `#v[v₁, v₂, v₃]` -/
def mkVector3 (v₁ v₂ v₃ : α) : Vector α 3:=
  mkEmpty 3
    |> push v₁
    |> push v₂
    |> push v₃


/-- Create vector `#v[v₁, v₂, v₃, v₄]` -/
def mkVector4 (v₁ v₂ v₃ v₄ : α) : Vector α 4:=
  mkEmpty 4
    |> push v₁
    |> push v₂
    |> push v₃
    |> push v₄

/-- Create vector `#v[v₁, v₂, v₃, v₄, v₅]` -/
def mkVector5 (v₁ v₂ v₃ v₄ v₅ : α) : Vector α 5 :=
  mkEmpty 5
    |> push v₁
    |> push v₂
    |> push v₃
    |> push v₄
    |> push v₅

/-- Create vector `#v[v₁, v₂, v₃, v₄, v₅, v₆]` -/
def mkVector6 (v₁ v₂ v₃ v₄ v₅ v₆ : α) : Vector α 6 :=
  mkEmpty 6
    |> push v₁
    |> push v₂
    |> push v₃
    |> push v₄
    |> push v₅
    |> push v₆

/-- Create vector `#v[v₁, v₂, v₃, v₄, v₅, v₆, v₇]` -/
def mkVector7 (v₁ v₂ v₃ v₄ v₅ v₆ v₇ : α) : Vector α 7 :=
  mkEmpty 7
    |> push v₁
    |> push v₂
    |> push v₃
    |> push v₄
    |> push v₅
    |> push v₆
    |> push v₇

/-- Create vector `#v[v₁, v₂, v₃, v₄, v₅, v₆, v₇, v₈]` -/
def mkVector8 (v₁ v₂ v₃ v₄ v₅ v₆ v₇ v₈ : α) : Vector α 8 :=
  mkEmpty 8
    |> push v₁
    |> push v₂
    |> push v₃
    |> push v₄
    |> push v₅
    |> push v₆
    |> push v₇
    |> push v₈


end Vector

/-- Unexpander for `Vector.empty` function -/
@[app_unexpander Vector.empty] def unexpandVectorEmpty : Lean.PrettyPrinter.Unexpander
  | _ => `(#v[])

/-- Unexpander for `Vector.mkVector0` function -/
@[app_unexpander Array.mkArray0] def unexpandMkVector0 : Lean.PrettyPrinter.Unexpander
  | _ => `(#v[])

/-- Unexpander for `Vector.mkVector1` function -/
@[app_unexpander Array.mkArray1] def unexpandMkVector1 : Lean.PrettyPrinter.Unexpander
  | `($(_) $a1) => `(#v[$a1])
  | _ => throw ()

/-- Unexpander for `Vector.mkVector2` function -/
@[app_unexpander Array.mkArray2] def unexpandMkVector2 : Lean.PrettyPrinter.Unexpander
  | `($(_) $a1 $a2) => `(#v[$a1, $a2])
  | _ => throw ()

/-- Unexpander for `Vector.mkVector3` function -/
@[app_unexpander Array.mkArray3] def unexpandMkVector3 : Lean.PrettyPrinter.Unexpander
  | `($(_) $a1 $a2 $a3) => `(#v[$a1, $a2, $a3])
  | _ => throw ()

/-- Unexpander for `Vector.mkVector4` function -/
@[app_unexpander Array.mkArray4] def unexpandMkVector4 : Lean.PrettyPrinter.Unexpander
  | `($(_) $a1 $a2 $a3 $a4) => `(#v[$a1, $a2, $a3, $a4])
  | _ => throw ()

/-- Unexpander for `Vector.mkVector5` function -/
@[app_unexpander Array.mkArray5] def unexpandMkVector5 : Lean.PrettyPrinter.Unexpander
  | `($(_) $a1 $a2 $a3 $a4 $a5) => `(#v[$a1, $a2, $a3, $a4, $a5])
  | _ => throw ()

/-- Unexpander for `Vector.mkVector6` function -/
@[app_unexpander Array.mkArray6] def unexpandMkVector6 : Lean.PrettyPrinter.Unexpander
  | `($(_) $a1 $a2 $a3 $a4 $a5 $a6) => `(#v[$a1, $a2, $a3, $a4, $a5, $a6])
  | _ => throw ()

/-- Unexpander for `Vector.mkVector7` function -/
@[app_unexpander Array.mkArray7] def unexpandMkVector7 : Lean.PrettyPrinter.Unexpander
  | `($(_) $a1 $a2 $a3 $a4 $a5 $a6 $a7) => `(#v[$a1, $a2, $a3, $a4, $a5, $a6, $a7])
  | _ => throw ()

/-- Unexpander for `Vector.mkVector8` function -/
@[app_unexpander Array.mkArray8] def unexpandMkVector8 : Lean.PrettyPrinter.Unexpander
  | `($(_) $a1 $a2 $a3 $a4 $a5 $a6 $a7 $a8) => `(#v[$a1, $a2, $a3, $a4, $a5, $a6, $a7, $a8])
  | _ => throw ()
