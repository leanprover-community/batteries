/-
Copyright (c) 2024 Shreyas Srinivas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shreyas Srinivas, François G. Dorais
-/

import Batteries.Data.Vector.Basic
import Batteries.Data.List.Basic
import Batteries.Data.List.Lemmas
import Batteries.Data.Array.Lemmas
import Batteries.Tactic.Lint.Simp

namespace Batteries

namespace Vector

theorem toArray_injective : ∀ {v w : Vector α n}, v.toArray = w.toArray → v = w
  | {..}, {..}, rfl => rfl

@[ext]
protected theorem ext {a b : Vector α n} (h : (i : Nat) → (_ : i < n) → a[i] = b[i]) : a = b := by
  apply Vector.toArray_injective
  apply Array.ext
  · rw [a.size_toArray, b.size_toArray]
  · intro i hi _
    rw [a.size_toArray] at hi
    exact h i hi

/-! ### mk lemmas -/

theorem toArray_mk (a : Array α) (h : a.size = n) : (Vector.mk a h).toArray = a := rfl

@[simp] theorem allDiff_mk [BEq α] (a : Array α) (h : a.size = n) :
    (Vector.mk a h).allDiff = a.allDiff := rfl

@[simp] theorem mk_append_mk (a b : Array α) (ha : a.size = n) (hb : b.size = m) :
    Vector.mk a ha ++ Vector.mk b hb = Vector.mk (a ++ b) (by simp [ha, hb]) := rfl

@[simp] theorem back!_mk [Inhabited α] (a : Array α) (h : a.size = n) :
    (Vector.mk a h).back! = a.back! := rfl

@[simp] theorem back?_mk (a : Array α) (h : a.size = n) :
    (Vector.mk a h).back? = a.back? := rfl

@[simp] theorem drop_mk (a : Array α) (h : a.size = n) (m) :
    (Vector.mk a h).drop m = Vector.mk (a.extract m a.size) (by simp [h]) := rfl

@[simp] theorem eraseIdx!_mk (a : Array α) (h : a.size = n) (i) (hi : i < n) :
    (Vector.mk a h).eraseIdx! i = Vector.mk (a.eraseIdx! i) (by simp [h, hi]) := by
  simp [Vector.eraseIdx!, hi]

@[simp] theorem feraseIdx_mk (a : Array α) (h : a.size = n) (i) :
    (Vector.mk a h).feraseIdx i = Vector.mk (a.feraseIdx (i.cast h.symm)) (by simp [h]) := rfl

@[simp] theorem extract_mk (a : Array α) (h : a.size = n) (start stop) :
    (Vector.mk a h).extract start stop = Vector.mk (a.extract start stop) (by simp [h]) := rfl

@[simp] theorem getElem_mk (a : Array α) (h : a.size = n) (i) (hi : i < n) :
    (Vector.mk a h)[i] = a[i] := rfl

@[simp] theorem get_mk (a : Array α) (h : a.size = n) (i) :
    (Vector.mk a h).get i = a.get (i.cast h.symm) := rfl

@[simp] theorem getD_mk (a : Array α) (h : a.size = n) (i x) :
    (Vector.mk a h).getD i x = a.getD i x := rfl

@[simp] theorem uget_mk (a : Array α) (h : a.size = n) (i) (hi : i.toNat < n) :
    (Vector.mk a h).uget i hi = a.uget i (by simp [h, hi]) := rfl

@[simp] theorem indexOf?_mk [BEq α] (a : Array α) (h : a.size = n) (x : α) :
    (Vector.mk a h).indexOf? x = (a.indexOf? x).map (Fin.cast h) := rfl

@[simp] theorem mk_isEqv_mk (r : α → α → Bool) (a b : Array α) (ha : a.size = n) (hb : b.size = n) :
    Vector.isEqv (Vector.mk a ha) (Vector.mk b hb) r = Array.isEqv a b r := by
  simp [Vector.isEqv, Array.isEqv, ha, hb]

@[simp] theorem mk_isPrefixOf_mk [BEq α] (a b : Array α) (ha : a.size = n) (hb : b.size = m) :
    (Vector.mk a ha).isPrefixOf (Vector.mk b hb) = a.isPrefixOf b := rfl

@[simp] theorem map_mk (a : Array α) (h : a.size = n) (f : α → β) :
    (Vector.mk a h).map f = Vector.mk (a.map f) (by simp [h]) := rfl

@[simp] theorem pop_mk (a : Array α) (h : a.size = n) :
    (Vector.mk a h).pop = Vector.mk a.pop (by simp [h]) := rfl

@[simp] theorem push_mk (a : Array α) (h : a.size = n) (x) :
    (Vector.mk a h).push x = Vector.mk (a.push x) (by simp [h]) := rfl

@[simp] theorem reverse_mk (a : Array α) (h : a.size = n) :
    (Vector.mk a h).reverse = Vector.mk a.reverse (by simp [h]) := rfl

@[simp] theorem set_mk (a : Array α) (h : a.size = n) (i x) :
    (Vector.mk a h).set i x = Vector.mk (a.set (i.cast h.symm) x) (by simp [h]) := rfl

@[simp] theorem set!_mk (a : Array α) (h : a.size = n) (i x) :
    (Vector.mk a h).set! i x = Vector.mk (a.set! i x) (by simp [h]) := rfl

@[simp] theorem setD_mk (a : Array α) (h : a.size = n) (i x) :
    (Vector.mk a h).setD i x = Vector.mk (a.setD i x) (by simp [h]) := rfl

@[simp] theorem setN_mk (a : Array α) (h : a.size = n) (i x) (hi : i < n) :
    (Vector.mk a h).setN i x = Vector.mk (a.setN i x) (by simp [h]) := rfl

@[simp] theorem swap_mk (a : Array α) (h : a.size = n) (i j) :
    (Vector.mk a h).swap i j = Vector.mk (a.swap (i.cast h.symm) (j.cast h.symm)) (by simp [h]) :=
  rfl

@[simp] theorem swap!_mk (a : Array α) (h : a.size = n) (i j) :
    (Vector.mk a h).swap! i j = Vector.mk (a.swap! i j) (by simp [h]) := rfl

@[simp] theorem swapN_mk (a : Array α) (h : a.size = n) (i j) (hi : i < n) (hj : j < n) :
    (Vector.mk a h).swapN i j = Vector.mk (a.swapN i j) (by simp [h]) := rfl

@[simp] theorem swapAt_mk (a : Array α) (h : a.size = n) (i x) : (Vector.mk a h).swapAt i x =
    ((a.swapAt (i.cast h.symm) x).fst, Vector.mk (a.swapAt (i.cast h.symm) x).snd (by simp [h])) :=
  rfl

@[simp] theorem swapAt!_mk (a : Array α) (h : a.size = n) (i x) : (Vector.mk a h).swapAt! i x =
    ((a.swapAt! i x).fst, Vector.mk (a.swapAt! i x).snd (by simp [h])) := rfl

@[simp] theorem swapAtN_mk (a : Array α) (h : a.size = n) (i x) (hi : i < n) :
    (Vector.mk a h).swapAtN i x =
      ((a.swapAtN i x).fst, Vector.mk (a.swapAtN i x).snd (by simp [h])) := rfl

@[simp] theorem take_mk (a : Array α) (h : a.size = n) (m) :
    (Vector.mk a h).take m = Vector.mk (a.take m) (by simp [h]) := rfl

@[simp] theorem mk_zipWith_mk (f : α → β → γ) (a : Array α) (b : Array β)
      (ha : a.size = n) (hb : b.size = n) : zipWith (Vector.mk a ha) (Vector.mk b hb) f =
        Vector.mk (Array.zipWith a b f) (by simp [ha, hb]) := rfl

@[simp] theorem getElem_toArray {α n} (xs : Vector α n) (i : Nat) (h : i < xs.toArray.size) :
    xs.toArray[i] = xs[i]'(by simpa using h) := by
  cases xs; simp

/-! ### toArray lemmas -/

@[simp] theorem toArray_append (a : Vector α m) (b : Vector α n) :
    (a ++ b).toArray = a.toArray ++ b.toArray := rfl

@[simp] theorem toArray_drop (a : Vector α n) (m) :
    (a.drop m).toArray = a.toArray.extract m a.size := rfl

@[simp] theorem toArray_empty : (Vector.empty (α := α)).toArray = #[] := rfl

@[simp] theorem toArray_mkEmpty (cap) :
    (Vector.mkEmpty (α := α) cap).toArray = Array.mkEmpty cap := rfl

@[simp] theorem toArray_eraseIdx! (a : Vector α n) (i) (hi : i < n) :
    (a.eraseIdx! i).toArray = a.toArray.eraseIdx! i := by
  cases a; simp [hi]

@[simp] theorem toArray_eraseIdxN (a : Vector α n) (i) (hi : i < n) :
    (a.eraseIdxN i).toArray = a.toArray.eraseIdxN i (by simp [hi]) := rfl

@[simp] theorem toArray_feraseIdx (a : Vector α n) (i) :
    (a.feraseIdx i).toArray = a.toArray.feraseIdx (i.cast a.size_toArray.symm) := rfl

@[simp] theorem toArray_extract (a : Vector α n) (start stop) :
    (a.extract start stop).toArray = a.toArray.extract start stop := rfl

@[simp] theorem toArray_map (f : α → β) (a : Vector α n) :
    (a.map f).toArray = a.toArray.map f := rfl

@[simp] theorem toArray_ofFn (f : Fin n → α) : (Vector.ofFn f).toArray = Array.ofFn f := rfl

@[simp] theorem toArray_pop (a : Vector α n) : a.pop.toArray = a.toArray.pop := rfl

@[simp] theorem toArray_push (a : Vector α n) (x) : (a.push x).toArray = a.toArray.push x := rfl

@[simp] theorem toArray_range : (Vector.range n).toArray = Array.range n := rfl

@[simp] theorem toArray_reverse (a : Vector α n) : a.reverse.toArray = a.toArray.reverse := rfl

@[simp] theorem toArray_set (a : Vector α n) (i x) :
    (a.set i x).toArray = a.toArray.set (i.cast a.size_toArray.symm) x := rfl

@[simp] theorem toArray_set! (a : Vector α n) (i x) :
    (a.set! i x).toArray = a.toArray.set! i x := rfl

@[simp] theorem toArray_setD (a : Vector α n) (i x) :
    (a.setD i x).toArray = a.toArray.setD i x := rfl

@[simp] theorem toArray_setN (a : Vector α n) (i x) (hi : i < n) :
    (a.setN i x).toArray = a.toArray.setN i x (by simp [hi]) := rfl

@[simp] theorem toArray_singleton (x : α) : (Vector.singleton x).toArray = #[x] := rfl

@[simp] theorem toArray_swap (a : Vector α n) (i j) : (a.swap i j).toArray =
    a.toArray.swap (i.cast a.size_toArray.symm) (j.cast a.size_toArray.symm) := rfl

@[simp] theorem toArray_swap! (a : Vector α n) (i j) :
    (a.swap! i j).toArray = a.toArray.swap! i j := rfl

@[simp] theorem toArray_swapN (a : Vector α n) (i j) (hi : i < n) (hj : j < n) :
    (a.swapN i j).toArray = a.toArray.swapN i j (by simp [hi]) (by simp [hj]) := rfl

@[simp] theorem toArray_swapAt (a : Vector α n) (i x) :
    ((a.swapAt i x).fst, (a.swapAt i x).snd.toArray) =
      ((a.toArray.swapAt (i.cast a.size_toArray.symm) x).fst,
        (a.toArray.swapAt (i.cast a.size_toArray.symm) x).snd) := rfl

@[simp] theorem toArray_swapAt! (a : Vector α n) (i x) :
    ((a.swapAt! i x).fst, (a.swapAt! i x).snd.toArray) =
      ((a.toArray.swapAt! i x).fst, (a.toArray.swapAt! i x).snd) := rfl

@[simp] theorem toArray_swapAtN (a : Vector α n) (i x) (hi : i < n) :
    ((a.swapAtN i x).fst, (a.swapAtN i x).snd.toArray) =
      ((a.toArray.swapAtN i x (by simp [hi])).fst,
        (a.toArray.swapAtN i x (by simp [hi])).snd) := rfl

@[simp] theorem toArray_take (a : Vector α n) (m) : (a.take m).toArray = a.toArray.take m := rfl

@[simp] theorem toArray_zipWith (f : α → β → γ) (a : Vector α n) (b : Vector β n) :
    (Vector.zipWith a b f).toArray = Array.zipWith a.toArray b.toArray f := rfl

/-! ### toList lemmas -/

theorem length_toList {α n} (xs : Vector α n) : xs.toList.length = n := by simp

theorem getElem_toList {α n} (xs : Vector α n) (i : Nat) (h : i < xs.toList.length) :
    xs.toList[i] = xs[i]'(by simpa using h) := by simp

/-! ### getElem lemmas -/

@[simp] theorem getElem_ofFn {α n} (f : Fin n → α) (i : Nat) (h : i < n) :
    (Vector.ofFn f)[i] = f ⟨i, by simpa using h⟩ := by
  simp [ofFn]

@[simp] theorem getElem_push_last {v : Vector α n} {x : α} : (v.push x)[n] = x := by
  rcases v with ⟨_, rfl⟩; simp

-- The `simpNF` linter incorrectly claims that this lemma can not be applied by `simp`.
@[simp, nolint simpNF] theorem getElem_push_lt {v : Vector α n} {x : α} {i : Nat} (h : i < n) :
    (v.push x)[i] = v[i] := by
  rcases v with ⟨_, rfl⟩; simp [Array.getElem_push_lt, h]

@[simp] theorem getElem_pop {v : Vector α n} {i : Nat} (h : i < n - 1) : (v.pop)[i] = v[i] := by
  rcases v with ⟨_, rfl⟩; simp

/--
Variant of `getElem_pop` that will sometimes fire when `getElem_pop` gets stuck because of
defeq issues in the implicit size argument.
-/
@[simp] theorem getElem_pop' (v : Vector α (n + 1)) (i : Nat) (h : i < n + 1 - 1) :
    @getElem (Vector α n) Nat α (fun _ i => i < n) instGetElemNatLt v.pop i h = v[i] :=
  getElem_pop h

@[simp] theorem push_pop_back (v : Vector α (n + 1)) : v.pop.push v.back = v := by
  ext i
  by_cases h : i < n
  · simp [h]
  · replace h : i = v.size - 1 := by rw [size_toArray]; omega
    subst h
    simp [pop, back, back!, ← Array.eq_push_pop_back!_of_size_ne_zero]

/-! ### empty lemmas -/

@[simp] theorem map_empty (f : α → β) : map f empty = empty := by
  apply toArray_injective; simp

protected theorem eq_empty (v : Vector α 0) : v = empty := by
  apply toArray_injective
  apply Array.eq_empty_of_size_eq_zero v.2

/-! ### Decidable quantifiers. -/

theorem forall_zero_iff {P : Vector α 0 → Prop} :
    (∀ v, P v) ↔ P .empty := by
  constructor
  · intro h
    apply h
  · intro h v
    obtain (rfl : v = .empty) := (by ext i h; simp at h)
    apply h

theorem forall_cons_iff {P : Vector α (n + 1) → Prop} :
    (∀ v : Vector α (n + 1), P v) ↔ (∀ (x : α) (v : Vector α n), P (v.push x)) := by
  constructor
  · intro h _ _
    apply h
  · intro h v
    have w : v = v.pop.push v.back := by simp
    rw [w]
    apply h

instance instDecidableForallVectorZero (P : Vector α 0 → Prop) :
    ∀ [Decidable (P .empty)], Decidable (∀ v, P v)
  | .isTrue h => .isTrue fun ⟨v, s⟩ => by
    obtain (rfl : v = .empty) := (by ext i h₁ h₂; exact s; cases h₂)
    exact h
  | .isFalse h => .isFalse (fun w => h (w _))

instance instDecidableForallVectorSucc (P : Vector α (n+1) → Prop)
    [Decidable (∀ (x : α) (v : Vector α n), P (v.push x))] : Decidable (∀ v, P v) :=
  decidable_of_iff' (∀ x (v : Vector α n), P (v.push x)) forall_cons_iff

instance instDecidableExistsVectorZero (P : Vector α 0 → Prop) [Decidable (P .empty)] :
    Decidable (∃ v, P v) :=
  decidable_of_iff (¬ ∀ v, ¬ P v) Classical.not_forall_not

instance instDecidableExistsVectorSucc (P : Vector α (n+1) → Prop)
    [Decidable (∀ (x : α) (v : Vector α n), ¬ P (v.push x))] : Decidable (∃ v, P v) :=
  decidable_of_iff (¬ ∀ v, ¬ P v) Classical.not_forall_not
