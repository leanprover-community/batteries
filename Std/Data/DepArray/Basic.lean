import Std.Data.Array.Basic
import Std.Data.Array.Lemmas
import Std.Data.Fin.Lemmas
import Std.Util.TypeErased

/-! # DepArray
Array whose element types depend on the index of the element. -/

namespace Std

/-- (Index-)Dependent arrays. -/
structure DepArray (size : Nat) (τ : Fin size → Type u) : Type u where
  /-- The underlying, untyped data -/
  data : Array TypeErased.{u}
  /-- `data` is the correct size -/
  h_size : size = data.size
  /-- The elements of `data` have types as described by `τ`. -/
  h_tys : ∀ i, (data[i.cast h_size]).type = τ i

namespace DepArray

/-- Get the value at index `i`. -/
def get (i : Fin size) (A : DepArray size τ) : τ i :=
  A.data[i.cast A.h_size] |>.cast (A.h_tys i)

/-- Build a `DepArray size τ` from a dependent function on its indices. -/
def ofFn (size : Nat) (τ : Fin size → Type u) (f : (i : Fin size) → τ i) : DepArray size τ where
  data := Array.ofFn (fun i => TypeErased.mk <| f i)
  h_size := by simp
  h_tys := by simp

@[simp] theorem get_ofFn (size τ) (f : (i : Fin size) → τ i) (i) : get i (ofFn size τ f) = f i := by
  simp [get, ofFn, cast]

/-- Set index `i` to `x`. See `set'` for a version which modifies the type at `i` as well. -/
def set (i : Fin size) (x : τ i) (A : DepArray size τ) : DepArray size τ where
  data := A.data.set (i.cast A.h_size) (.mk x)
  h_size := by simp; exact A.h_size
  h_tys := by
    intro j; simp; rw [Array.get_set]
    cases i; cases j
    split
    . simp at *; simp [*]
    . simp; rw [←A.h_tys]; congr; intro j i _; exact A.h_size ▸ j.isLt

theorem get_set (A : DepArray size τ) (i x j) : (set i x A).get j = if h : i = j then h ▸ x else A.get j := by
  simp [get, set]
  cases A; next data h_size h_tys =>
  cases h_size
  simp
  split
  next h =>
    cases h; cases i
    rw [TypeErased.cast_rw _ (Array.get_set ..)]
    . simp [cast]
    . simp [*]
  next h =>
    congr 1
    apply Array.get_set_ne
    simp [Fin.val_ne_of_ne h]

/-- Set index `i` to `x`.

NB: This changes the type at index `i`. See `set` for a version which does not change the type. -/
def set' (i : Fin size) (x : β) (A : DepArray size τ) : DepArray size (fun j => if i = j then β else τ j) where
  data := A.data.set (i.cast A.h_size) (.mk x)
  h_size := by simp; exact A.h_size
  h_tys := by
    intro j; simp; rw [Array.get_set]
    cases i; cases j
    split
    . simp at *; simp [*]
    . simp at *; simp [*]; rw [←A.h_tys]; congr; intro j _; exact A.h_size ▸ j.isLt

theorem cast_compose (h1 : β = γ) (h2 : α = β) (x : α) : cast h1 (cast h2 x) = (cast (h2.trans h1) x) := by
  cases h1; cases h2; simp [cast]

@[simp] theorem get_set'_eq (A : DepArray size τ) (i) (x : β) : (set' i x A).get i = cast (by simp) x := by
  simp [get, set']
  rw [TypeErased.cast_rw _ (Array.get_set ..)]
  . simp
  . exact A.h_size ▸ i.isLt

@[simp] theorem get_set'_ne (A : DepArray size τ) (i) (x : β) (j) (h : i ≠ j)
  : (set' i x A).get j = cast (by simp [h]) (A.get j) := by
  simp [get, set']
  congr 1
  apply Array.get_set_ne
  simp [Fin.val_ne_of_ne h]
