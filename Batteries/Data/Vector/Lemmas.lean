/-
Copyright (c) 2024 Shreyas Srinivas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shreyas Srinivas, François G. Dorais, Eric Wieser
-/
module

public import Batteries.Data.Array.Basic
public import Batteries.Data.Array.Scan
public import Batteries.Data.List.Scan
public import Batteries.Data.Vector.Basic

@[expose] public section

namespace Vector

theorem toArray_injective : ∀ {v w : Vector α n}, v.toArray = w.toArray → v = w
  | {..}, {..}, rfl => rfl

/-! ### mk lemmas -/

@[simp] theorem get_mk (a : Array α) (h : a.size = n) (i) :
    (Vector.mk a h).get i = a[i] := rfl

@[simp] theorem getD_mk (a : Array α) (h : a.size = n) (i x) :
    (Vector.mk a h).getD i x = a.getD i x := rfl

@[simp] theorem uget_mk (a : Array α) (h : a.size = n) (i) (hi : i.toNat < n) :
    (Vector.mk a h).uget i hi = a.uget i (by simp [h, hi]) := rfl

/-! ### tail lemmas -/

theorem tail_eq_of_zero {v : Vector α 0} : v.tail = #v[] := Vector.eq_empty

theorem tail_eq_of_ne_zero [NeZero n] {v : Vector α n} :
    v.tail = v.eraseIdx 0 n.pos_of_neZero := by
  simp only [tail_eq_cast_extract]
  ext
  simp only [getElem_cast, getElem_extract, getElem_eraseIdx, Nat.not_lt_zero, ↓reduceDIte]
  congr 1
  omega

-- This is not a `@[simp]` lemma because the LHS simplifies to `Vector.extract`.
theorem toList_tail {v : Vector α n} :
    v.tail.toList = v.toList.tail :=
  match n with
  | 0 => by simp [Vector.eq_empty]
  | _ + 1 => by
    apply List.ext_getElem
    · simp
    · intro i h₁ h₂
      simp only [Nat.add_one_sub_one, tail_eq_cast_extract, getElem_toList, getElem_cast,
        getElem_extract, List.getElem_tail]
      congr 1
      omega

/-! ### getElem lemmas -/

theorem getElem_tail {v : Vector α n} {i : Nat} (hi : i < n - 1) :
    v.tail[i] = v[i + 1] :=
  match n with
  | _ + 1 =>
    getElem_congr_coll tail_eq_of_ne_zero |>.trans <|
    getElem_eraseIdx (Nat.zero_lt_succ _) hi

/-! ### get lemmas -/

theorem get_eq_getElem (v : Vector α n) (i : Fin n) : v.get i = v[(i : Nat)] := rfl

@[simp] theorem get_push_last (v : Vector α n) (a : α) :
    (v.push a).get (Fin.last n) = a :=
  getElem_push_last

@[simp] theorem get_push_castSucc (v : Vector α n) (a : α) (i : Fin n) :
    (v.push a).get (Fin.castSucc i) = v.get i :=
  getElem_push_lt _

@[simp] theorem get_map (v : Vector α n) (f : α → β) (i : Fin n) :
    (v.map f).get i = f (v.get i) :=
  getElem_map _ _

@[simp] theorem get_reverse (v : Vector α n) (i : Fin n) :
    v.reverse.get i = v.get (i.rev) :=
  getElem_reverse _ |>.trans <| congrArg v.get <| Fin.ext <| by simp; omega

@[simp] theorem get_replicate (n : Nat) (a : α) (i : Fin n) : (replicate n a).get i = a :=
  getElem_replicate _

@[simp] theorem get_range (n : Nat) (i : Fin n) : (range n).get i = i :=
  getElem_range _

@[simp] theorem get_ofFn (f : Fin n → α) (i : Fin n) : (ofFn f).get i = f i :=
  getElem_ofFn _

@[simp] theorem get_cast (v : Vector α m) (h : m = n) (i : Fin n) :
    (v.cast h).get i = v.get (i.cast h.symm) :=
  getElem_cast _

-- This is not a `@[simp]` lemma because the LHS simplifies to `Vector.extract`.
theorem get_tail (v : Vector α (n + 1)) (i : Fin n) :
    v.tail.get i = v.get i.succ := getElem_tail _

/-! ### finIdxOf? lemmas -/

@[simp]
theorem finIdxOf?_empty [BEq α] (v : Vector α 0) : v.finIdxOf? a = none := by
  simp [v.eq_empty]

@[simp]
theorem finIdxOf?_eq_none_iff [BEq α] [LawfulBEq α] {v : Vector α n} {a : α} :
    v.finIdxOf? a = none ↔ a ∉ v := by
  obtain ⟨xs, rfl⟩ := v
  simp

@[simp]
theorem finIdxOf?_eq_some_iff [BEq α] [LawfulBEq α] {v : Vector α n} {a : α} {i : Fin n} :
    v.finIdxOf? a = some i ↔ v.get i = a ∧ ∀ j < i, ¬v.get j = a := by
  obtain ⟨xs, rfl⟩ := v
  simp

@[simp]
theorem isSome_finIdxOf? [BEq α] [PartialEquivBEq α] {v : Vector α n} {a : α} :
    (v.finIdxOf? a).isSome = v.contains a := by
  obtain ⟨v, rfl⟩ := v
  simp

@[simp]
theorem isNone_finIdxOf? [BEq α] [PartialEquivBEq α] {v : Vector α n} {a : α} :
    (v.finIdxOf? a).isNone = !v.contains a := by
  obtain ⟨v, rfl⟩ := v
  simp

private theorem scanlM.loop_toArray [Monad m] [LawfulMonad m] (f : β → α → m β) (as : Vector α n)
    (h_stop : n ≤ as.toArray.size) (i : Nat) (hi : i ≤ n) (cur : β)
    (acc_v : Vector β i) (acc_a : Array β) (h_acc : acc_v.toArray = acc_a) :
    Vector.toArray <$> Vector.scanlM.loop f as cur i hi acc_v =
    Array.scanlM.loop f cur as.toArray i n h_stop acc_a := by
  induction h_term : n - i generalizing i cur acc_v acc_a with
  | zero =>
    unfold Vector.scanlM.loop Array.scanlM.loop
    simp [h_acc, show i = n by omega]
  | succ k ih =>
    unfold Vector.scanlM.loop Array.scanlM.loop
    simp only [show i < n by omega, dite_true, map_bind]
    apply bind_congr
    intro next
    apply ih
    . simp [Vector.toArray_push, h_acc]
    . omega

theorem toArray_scanlM [Monad m] [LawfulMonad m] {f : β → α → m β} {as : Vector α n} :
    Vector.toArray <$> as.scanlM f init = as.toArray.scanlM f init := by
  simp_all [scanlM.loop_toArray, scanlM, Array.scanlM]

private theorem scanrM.loop_toArray [Monad m] [LawfulMonad m] {f : α → β → m β}
    {as : Vector α n} {i : Nat} {hi : i ≤ n} {acc_v : Vector β (n - i)}
    {acc_a : Array β} {h_acc : acc_v.toArray = acc_a} :
    Vector.toArray <$> Vector.scanrM.loop f as cur i hi acc_v =
    Array.scanrM.loop f cur as.toArray i 0 (by simp; omega) acc_a := by
  induction i generalizing cur acc_a with
  | zero =>
    unfold Vector.scanrM.loop Array.scanrM.loop
    simp [h_acc]
  | succ k ih =>
    unfold Vector.scanrM.loop Array.scanrM.loop
    simp only [Nat.zero_lt_succ k, dite_true, map_bind]
    apply bind_congr
    intro next
    apply ih
    simp [Vector.toArray_push, Vector.toArray_cast, h_acc]

theorem toArray_scanrM [Monad m] [LawfulMonad m] {f : α → β → m β} {as : Vector α n} :
    Vector.toArray <$> as.scanrM f init = as.toArray.scanrM f init := by
  simp_all [scanrM, Array.scanrM, scanrM.loop_toArray]

/-! ### scanlM/scanrM lemmas -/

@[simp, grind =]
theorem toList_scanlM [Monad m] [LawfulMonad m] {f : β → α → m β} {as : Vector α n} :
    Vector.toList <$> as.scanlM f init = as.toList.scanlM f init := by
  unfold toList
  rw [← Functor.map_map]
  simp only [toArray_scanlM, Array.toList_scanlM, toList_toArray]

@[simp, grind =]
theorem toList_scanrM [Monad m] [LawfulMonad m] {f : α → β → m β} {as : Vector α n} :
    Vector.toList <$> as.scanrM f init = as.toList.scanrM f init := by
  unfold toList
  rw [← Functor.map_map]
  simp only [toArray_scanrM, Array.toList_scanrM, toList_toArray]

@[simp, grind =]
theorem scanlM_empty [Monad m] [LawfulMonad m] {f : β → α → m β} :
    (#v[] : Vector α 0).scanlM f init = pure #v[init] := by
  rw [← _root_.map_inj_right toArray_inj.mp, toArray_scanlM]
  simp [Array.scanlM_empty]

@[simp, grind =]
theorem scanrM_empty [Monad m] [LawfulMonad m] {f : α → β → m β} :
    (#v[] : Vector α 0).scanrM f init = pure #v[init] := by
  rw [← _root_.map_inj_right toArray_inj.mp, toArray_scanrM]
  simp [Array.scanrM_empty]

theorem scanlM_reverse [Monad m] [LawfulMonad m] {f : β → α → m β} {as : Vector α n} :
    as.reverse.scanlM f init = Vector.reverse <$> (as.scanrM (flip f) init) := by
  rw [← _root_.map_inj_right toArray_inj.mp]
  simp only [Functor.map_map, toArray_scanlM, toArray_reverse,
    Array.scanlM_reverse, ← toArray_scanrM]

@[simp]
theorem scanlM_pure [Monad m] [LawfulMonad m] {f : β → α → β} {as : Vector α n} :
    as.scanlM (m := m) (pure <| f · ·) init = pure (as.scanl f init) := by
  rw [← _root_.map_inj_right toArray_inj.mp, toArray_scanlM, map_pure, Array.scanlM_pure]
  congr
  apply toArray_scanlM.symm

@[simp]
theorem scanrM_pure [Monad m] [LawfulMonad m] {f : α → β → β} {as : Vector α n} :
    as.scanrM (m := m) (pure <| f · ·) init = pure (as.scanr f init) := by
  rw [← _root_.map_inj_right toArray_inj.mp, toArray_scanrM, map_pure, Array.scanrM_pure]
  congr
  apply toArray_scanrM.symm

theorem idRun_scanlM {f : β → α → Id β} {as : Vector α n} :
    (as.scanlM f init).run = as.scanl (f · · |>.run) init :=
  scanlM_pure

theorem idRun_scanrM {f : α → β → Id β} {as : Vector α n} :
    (as.scanrM f init).run = as.scanr (f · · |>.run) init :=
  scanrM_pure

@[grind =]
theorem scanlM_map [Monad m] [LawfulMonad m] {f : α₁ → α₂} {g : β → α₂ → m β} {as : Vector α₁ n} :
    (as.map f).scanlM g init = as.scanlM (g · <| f ·) init := by
  rw [← _root_.map_inj_right toArray_inj.mp]
  simp only [toArray_scanlM, toArray_map, Array.scanlM_map]

@[grind =]
theorem scanrM_map [Monad m] [LawfulMonad m] {f : α₁ → α₂} {g : α₂ → β → m β} {as : Vector α₁ n} :
    (as.map f).scanrM g init = as.scanrM (fun a b => g (f a) b) init := by
  rw [← _root_.map_inj_right toArray_inj.mp]
  simp only [toArray_scanrM, toArray_map, Array.scanrM_map]

/-! ### scanl/scanr lemmas -/

theorem scanl_eq_scanlM {f : β → α → β} {as : Vector α n} :
    as.scanl f init = (as.scanlM (m := Id) (pure <| f · ·) init).run := by
  simp

theorem scanr_eq_scanrM {f : α → β → β} {as : Vector α n} :
    as.scanr f init = (as.scanrM (m := Id) (pure <| f · ·) init).run := by
  simp

theorem toArray_scanl {f : β → α → β} {as : Vector α n} :
    (as.scanl f init).toArray = as.toArray.scanl f init := by
  have h : Vector.toArray <$> (as.scanlM (m := Id) (pure <| f · ·) init) =
      as.toArray.scanlM (m := Id) (pure <| f · ·) init := toArray_scanlM ..
  simp only [scanl, Id.run]
  exact h

theorem toArray_scanr {f : α → β → β} {as : Vector α n} :
    (as.scanr f init).toArray = as.toArray.scanr f init := by
  have h : Vector.toArray <$> (as.scanrM (m := Id) (pure <| f · ·) init) =
      as.toArray.scanrM (m := Id) (pure <| f · ·) init := toArray_scanrM
  simp only [scanr, Id.run]
  exact h

@[simp, grind =]
theorem toList_scanl {f : β → α → β} {as : Vector α n} :
    (as.scanl f init).toList = as.toList.scanl f init := by
  rw [← toList_toArray, toArray_scanl, Array.toList_scanl, toList_toArray]

@[simp, grind =]
theorem toList_scanr {f : α → β → β} {as : Vector α n} :
    (as.scanr f init).toList = as.toList.scanr f init := by
  rw [← toList_toArray, toArray_scanr, Array.toList_scanr, toList_toArray]

@[grind =]
theorem scanl_empty {f : β → α → β} :
    (#v[] : Vector α 0).scanl f init = #v[init] := by
  apply toArray_inj.mp
  simp only [toArray_scanl, toArray_empty, Array.scanl_empty]

@[grind =]
theorem scanr_empty {f : α → β → β} :
    (#v[] : Vector α 0).scanr f init = #v[init] := by
  apply toArray_inj.mp
  simp only [toArray_scanr, toArray_empty, Array.scanr_empty]

@[grind =]
theorem scanl_singleton {f : β → α → β} {a : α} :
    (#v[a] : Vector α 1).scanl f init = #v[init, f init a] := by
  apply toArray_inj.mp
  simp only [toArray_scanl, Array.scanl_singleton]

@[simp, grind =]
theorem getElem_scanl {f : β → α → β} {as : Vector α n} (h : i < n + 1) :
    (as.scanl f init)[i] = (as.take i).foldl f init := by
  rw [← getElem_toArray, Vector.foldl]
  conv => lhs; arg 1; rw [toArray_scanl]
  apply Array.getElem_scanl
  simp [h]

@[simp, grind =]
theorem getElem_scanr {f : α → β → β} {as : Vector α n} (h : i < n + 1) :
    (as.scanr f init)[i] = (as.drop i).foldr f init := by
  rw [← getElem_toArray, Vector.foldr]
  conv => lhs; arg 1; rw [toArray_scanr]
  apply Array.getElem_scanr
  simp [h]

@[grind =]
theorem getElem?_scanl {f : β → α → β} {as : Vector α n} :
    (as.scanl f init)[i]? = if i ≤ n then some ((as.take i).foldl f init) else none := by
  rw [← getElem?_toArray, Vector.foldl]
  conv => lhs; arg 1; rw [toArray_scanl]
  conv => rhs; arg 1; rw [← Vector.size_toArray as]
  rw [Vector.toArray_take]
  apply Array.getElem?_scanl

@[grind =]
theorem getElem?_scanr {f : α → β → β} {as : Vector α n} :
    (as.scanr f init)[i]? = if i < n + 1 then some ((as.drop i).foldr f init)
      else none := by
  rw [← getElem?_toArray, Vector.foldr]
  conv => lhs; arg 1; rw [toArray_scanr]
  conv => rhs; arg 1; rw [← Vector.size_toArray as]
  unfold drop
  apply Array.getElem?_scanr

theorem getElem_scanl_zero {f : β → α → β} {as : Vector α n} :
    (as.scanl f init)[0] = init := by simp [foldl]

theorem getElem_scanr_zero {f : α → β → β} {as : Vector α n} :
    (as.scanr f init)[0] = as.foldr f init := by simp [foldr]

theorem getElem?_scanl_zero {f : β → α → β} {as : Vector α n} :
    (as.scanl f init)[0]? = some init := by simp [foldl]

theorem getElem?_scanr_zero {f : α → β → β} {as : Vector α n} :
    (as.scanr f init)[0]? = some (as.foldr f init) := by simp [foldr]

theorem getElem?_succ_scanl {f : β → α → β} {as : Vector α n} :
    (as.scanl f init)[i + 1]? = (as.scanl f init)[i]?.bind fun x => as[i]?.map fun y => f x y := by
  simp only [← getElem?_toArray, toArray_scanl, Array.getElem?_succ_scanl]

theorem getElem_succ_scanl {f : β → α → β} {as : Vector α n} (h : i + 1 < n + 1) :
    (as.scanl f init)[i + 1] = f (as.scanl f init)[i] as[i] := by
  repeat rw [← getElem_toList]
  conv => lhs; arg 1; rw [toList_scanl]
  conv => rhs; arg 1; arg 1; rw [toList_scanl]
  apply List.getElem_succ_scanl
  all_goals
    simp only [length_toList]
    omega

@[grind =]
theorem scanl_push {f : β → α → β} {as : Vector α n} {a : α} :
    (as.push a).scanl f init = (as.scanl f init).push (f (as.foldl f init) a) := by
  apply toArray_inj.mp
  simp only [toArray_scanl, toArray_push, Array.scanl_push, foldl]

@[grind =]
theorem scanr_push {f : α → β → β} {as : Vector α n} {a : α} :
    (as.push a).scanr f init = (as.scanr f (f a init)).push init := by
  apply toArray_inj.mp
  simp only [toArray_scanr, toArray_push, Array.scanr_push]

@[grind =]
theorem scanl_map {f : γ → β → γ} {g : α → β} {as : Vector α n} :
    (as.map g).scanl f init = as.scanl (f · <| g ·) init := by
  apply toArray_inj.mp
  simp only [toArray_scanl, toArray_map, Array.scanl_map]

@[grind =]
theorem scanr_map {f : β → γ → γ} {g : α → β} {as : Vector α n} :
    (as.map g).scanr f init = as.scanr (fun x acc => f (g x) acc) init := by
  apply toArray_inj.mp
  simp only [toArray_scanr, toArray_map, Array.scanr_map]

@[simp, grind =]
theorem back_scanl {f : β → α → β} {as : Vector α n} :
    (as.scanl f init).back = as.foldl f init := by
  rw [back, ← getElem_toArray]
  conv => lhs; arg 1; rw [toArray_scanl]
  conv => lhs; arg 2; rw [← Vector.size_toArray as, ← Array.size_scanl (f := f) init]
  rw [← Array.back_eq_getElem]
  apply Array.back_scanl
  . simp only [Array.size_scanl]
    omega
  . simp only [Vector.toArray_scanl, Array.size_scanl]
    rw [Vector.size_toArray as]
    omega

@[simp, grind =]
theorem back_scanr {f : α → β → β} {as : Vector α n} :
    (as.scanr f init).back = init := by
  rw [back, ← getElem_toArray]
  conv => lhs; arg 1; rw [toArray_scanr]
  conv => lhs; arg 2; rw [← Vector.size_toArray as, ← Array.size_scanr (f := f) init]
  rw [← Array.back_eq_getElem]
  apply Array.back_scanr
  . simp only [Array.size_scanr]
    omega
  . simp only [Vector.toArray_scanr, Array.size_scanr]
    rw [Vector.size_toArray as]
    omega

theorem back?_scanl {f : β → α → β} {as : Vector α n} :
    (as.scanl f init).back? = some (as.foldl f init) := by
  rw [back?_eq_getElem?, getElem?_eq_some_iff]
  constructor
  rw [← back_eq_getElem (xs := scanl f init as), back_scanl]

theorem back?_scanr {f : α → β → β} {as : Vector α n} :
    (as.scanr f init).back? = some init := by
  rw [back?_eq_getElem?, getElem?_eq_some_iff]
  constructor
  rw [← back_eq_getElem, back_scanr]

@[grind =]
theorem scanl_reverse {f : β → α → β} {as : Vector α n} :
    (as.reverse).scanl f init = (as.scanr (flip f) init).reverse := by
  apply toArray_inj.mp
  simp only [toArray_scanl, toArray_reverse, toArray_scanr, Array.scanl_reverse]

@[grind =]
theorem scanr_reverse {f : α → β → β} {as : Vector α n} :
    (as.reverse).scanr f init = (as.scanl (flip f) init).reverse := by
  apply toArray_inj.mp
  simp only [toArray_scanr, toArray_reverse, toArray_scanl, Array.scanr_reverse]
