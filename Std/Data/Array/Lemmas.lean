/-
Copyright (c) 2021 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Mario Carneiro, Gabriel Ebner
-/
import Std.Data.Nat.Lemmas
import Std.Data.List.Lemmas
import Std.Data.Array.Init.Lemmas
import Std.Data.Array.Basic
import Std.Tactic.SeqFocus
import Std.Util.ProofWanted

@[simp] theorem getElem_fin [GetElem Cont Nat Elem Dom] (a : Cont) (i : Fin n) (h : Dom a i) :
    a[i] = a[i.1] := rfl

@[simp] theorem getElem?_fin [GetElem Cont Nat Elem Dom] (a : Cont) (i : Fin n)
    [Decidable (Dom a i)] : a[i]? = a[i.1]? := rfl

@[simp] theorem getElem!_fin [GetElem Cont Nat Elem Dom] (a : Cont) (i : Fin n)
    [Decidable (Dom a i)] [Inhabited Elem] : a[i]! = a[i.1]! := rfl

theorem getElem?_pos [GetElem Cont Idx Elem Dom]
    (a : Cont) (i : Idx) (h : Dom a i) [Decidable (Dom a i)] : a[i]? = a[i] := dif_pos h

theorem getElem?_neg [GetElem Cont Idx Elem Dom]
    (a : Cont) (i : Idx) (h : ¬Dom a i) [Decidable (Dom a i)] : a[i]? = none := dif_neg h

@[simp] theorem mkArray_data (n : Nat) (v : α) : (mkArray n v).data = List.replicate n v := rfl

@[simp] theorem getElem_mkArray (n : Nat) (v : α) (h : i < (mkArray n v).size) :
    (mkArray n v)[i] = v := by simp [Array.getElem_eq_data_get]

namespace Array

attribute [simp] isEmpty uget

@[simp] theorem singleton_def (v : α) : singleton v = #[v] := rfl

@[simp] theorem toArray_data : (a : Array α) → a.data.toArray = a
  | ⟨l⟩ => ext' (data_toArray l)

@[simp] theorem data_length {l : Array α} : l.data.length = l.size := rfl

/-- # mem -/

theorem mem_data {a : α} {l : Array α} : a ∈ l.data ↔ a ∈ l := (mem_def _ _).symm

theorem not_mem_nil (a : α) : ¬ a ∈ #[] := nofun

/-- # get lemmas -/

theorem getElem?_mem {l : Array α} {i : Fin l.size} : l[i] ∈ l := by
  erw [Array.mem_def, getElem_eq_data_get]
  apply List.get_mem

theorem getElem_fin_eq_data_get (a : Array α) (i : Fin _) : a[i] = a.data.get i := rfl

@[simp] theorem ugetElem_eq_getElem (a : Array α) {i : USize} (h : i.toNat < a.size) :
  a[i] = a[i.toNat] := rfl

theorem getElem?_eq_getElem (a : Array α) (i : Nat) (h : i < a.size) : a[i]? = a[i] :=
  getElem?_pos ..

theorem get?_len_le (a : Array α) (i : Nat) (h : a.size ≤ i) : a[i]? = none := by
  simp [getElem?_neg, h]

theorem getElem_mem_data (a : Array α) (h : i < a.size) : a[i] ∈ a.data := by
  simp only [getElem_eq_data_get, List.get_mem]

theorem getElem?_eq_data_get? (a : Array α) (i : Nat) : a[i]? = a.data.get? i := by
  by_cases i < a.size <;> simp_all [getElem?_pos, getElem?_neg, List.get?_eq_get, eq_comm]; rfl

theorem get?_eq_data_get? (a : Array α) (i : Nat) : a.get? i = a.data.get? i :=
  getElem?_eq_data_get? ..

theorem get!_eq_get? [Inhabited α] (a : Array α) : a.get! n = (a.get? n).getD default := by
  simp [get!_eq_getD]

@[simp] theorem back_eq_back? [Inhabited α] (a : Array α) : a.back = a.back?.getD default := by
  simp [back, back?]

@[simp] theorem back?_push (a : Array α) : (a.push x).back? = some x := by
  simp [back?, getElem?_eq_data_get?]

theorem back_push [Inhabited α] (a : Array α) : (a.push x).back = x := by simp

theorem get?_push_lt (a : Array α) (x : α) (i : Nat) (h : i < a.size) :
    (a.push x)[i]? = some a[i] := by
  rw [getElem?_pos, get_push_lt]

theorem get?_push_eq (a : Array α) (x : α) : (a.push x)[a.size]? = some x := by
  rw [getElem?_pos, get_push_eq]

theorem get?_push {a : Array α} : (a.push x)[i]? = if i = a.size then some x else a[i]? := by
  split
  . next heq => rw [heq, getElem?_pos, get_push_eq]
  · next hne =>
    simp only [getElem?, size_push]
    split <;> split <;> try simp only [*, get_push_lt]
    · next p q => exact Or.elim (Nat.eq_or_lt_of_le (Nat.le_of_lt_succ p)) hne q
    · next p q => exact p (Nat.lt.step q)

@[simp] theorem get?_size {a : Array α} : a[a.size]? = none := by
  simp only [getElem?, Nat.lt_irrefl, dite_false]

@[simp] theorem data_set (a : Array α) (i v) : (a.set i v).data = a.data.set i.1 v := rfl

theorem get_set_eq (a : Array α) (i : Fin a.size) (v : α) :
    (a.set i v)[i.1] = v := by
  simp only [set, getElem_eq_data_get, List.get_set_eq]

theorem get?_set_eq (a : Array α) (i : Fin a.size) (v : α) :
    (a.set i v)[i.1]? = v := by simp [getElem?_pos, i.2]

@[simp] theorem get?_set_ne (a : Array α) (i : Fin a.size) {j : Nat} (v : α)
    (h : i.1 ≠ j) : (a.set i v)[j]? = a[j]? := by
  by_cases j < a.size <;> simp [getElem?_pos, getElem?_neg, *]

theorem get?_set (a : Array α) (i : Fin a.size) (j : Nat) (v : α) :
    (a.set i v)[j]? = if i.1 = j then some v else a[j]? := by
  if h : i.1 = j then subst j; simp [*] else simp [*]

theorem get_set (a : Array α) (i : Fin a.size) (j : Nat) (hj : j < a.size) (v : α) :
    (a.set i v)[j]'(by simp [*]) = if i = j then v else a[j] := by
  if h : i.1 = j then subst j; simp [*] else simp [*]

@[simp] theorem get_set_ne (a : Array α) (i : Fin a.size) {j : Nat} (v : α) (hj : j < a.size)
    (h : i.1 ≠ j) : (a.set i v)[j]'(by simp [*]) = a[j] := by
  simp only [set, getElem_eq_data_get, List.get_set_ne _ h]

theorem getElem_setD (a : Array α) (i : Nat) (v : α) (h : i < (setD a i v).size) :
  (setD a i v)[i] = v := by
  simp at h
  simp only [setD, h, dite_true, get_set, ite_true]

theorem set_set (a : Array α) (i : Fin a.size) (v v' : α) :
    (a.set i v).set ⟨i, by simp [i.2]⟩ v' = a.set i v' := by simp [set, List.set_set]

private theorem fin_cast_val (e : n = n') (i : Fin n) : e ▸ i = ⟨i.1, e ▸ i.2⟩ := by cases e; rfl

theorem swap_def (a : Array α) (i j : Fin a.size) :
    a.swap i j = (a.set i (a.get j)).set ⟨j.1, by simp [j.2]⟩ (a.get i) := by
  simp [swap, fin_cast_val]

theorem data_swap (a : Array α) (i j : Fin a.size) :
    (a.swap i j).data = (a.data.set i (a.get j)).set j (a.get i) := by simp [swap_def]

theorem get?_swap (a : Array α) (i j : Fin a.size) (k : Nat) : (a.swap i j)[k]? =
    if j = k then some a[i.1] else if i = k then some a[j.1] else a[k]? := by
  simp [swap_def, get?_set, ← getElem_fin_eq_data_get]

@[simp] theorem swapAt_def (a : Array α) (i : Fin a.size) (v : α) :
    a.swapAt i v = (a[i.1], a.set i v) := rfl

-- @[simp] -- FIXME: gives a weird linter error
theorem swapAt!_def (a : Array α) (i : Nat) (v : α) (h : i < a.size) :
    a.swapAt! i v = (a[i], a.set ⟨i, h⟩ v) := by simp [swapAt!, h]

@[simp] theorem data_pop (a : Array α) : a.pop.data = a.data.dropLast := by simp [pop]

@[simp] theorem pop_empty : (#[] : Array α).pop = #[] := rfl

@[simp] theorem pop_push (a : Array α) : (a.push x).pop = a := by simp [pop]

@[simp] theorem getElem_pop (a : Array α) (i : Nat) (hi : i < a.pop.size) :
    a.pop[i] = a[i]'(Nat.lt_of_lt_of_le (a.size_pop ▸ hi) (Nat.sub_le _ _)) :=
  List.get_dropLast ..

theorem eq_empty_of_size_eq_zero {as : Array α} (h : as.size = 0) : as = #[] := by
  apply ext
  · simp [h]
  · intros; contradiction

theorem eq_push_pop_back_of_size_ne_zero [Inhabited α] {as : Array α} (h : as.size ≠ 0) :
    as = as.pop.push as.back := by
  apply ext
  · simp [Nat.sub_add_cancel (Nat.zero_lt_of_ne_zero h)]
  · intros i h h'
    if hlt : i < as.pop.size then
      rw [get_push_lt (h:=hlt), getElem_pop]
    else
      have heq : i = as.pop.size :=
        Nat.le_antisymm (size_pop .. ▸ Nat.le_pred_of_lt h) (Nat.le_of_not_gt hlt)
      cases heq; rw [get_push_eq, back, ←size_pop, get!_eq_getD, getD, dif_pos h]; rfl

theorem eq_push_of_size_ne_zero {as : Array α} (h : as.size ≠ 0) :
    ∃ (bs : Array α) (c : α), as = bs.push c :=
  let _ : Inhabited α := ⟨as[0]⟩
  ⟨as.pop, as.back, eq_push_pop_back_of_size_ne_zero h⟩

theorem size_eq_length_data (as : Array α) : as.size = as.data.length := rfl

@[simp] theorem size_swap! (a : Array α) (i j) :
    (a.swap! i j).size = a.size := by unfold swap!; split <;> (try split) <;> simp [size_swap]

@[simp] theorem size_reverse (a : Array α) : a.reverse.size = a.size := by
  let rec go (as : Array α) (i j) : (reverse.loop as i j).size = as.size := by
    rw [reverse.loop]
    if h : i < j then
      have := reverse.termination h
      simp [(go · (i+1) ⟨j-1, ·⟩), h]
    else simp [h]
    termination_by j - i
  simp only [reverse]; split <;> simp [go]

@[simp] theorem size_range {n : Nat} : (range n).size = n := by
  unfold range
  induction n with
  | zero      => simp [Nat.fold]
  | succ k ih => rw [Nat.fold, flip]; simpa

@[simp] theorem reverse_data (a : Array α) : a.reverse.data = a.data.reverse := by
  let rec go (as : Array α) (i j hj)
      (h : i + j + 1 = a.size) (h₂ : as.size = a.size)
      (H : ∀ k, as.data.get? k = if i ≤ k ∧ k ≤ j then a.data.get? k else a.data.reverse.get? k)
      (k) : (reverse.loop as i ⟨j, hj⟩).data.get? k = a.data.reverse.get? k := by
    rw [reverse.loop]; dsimp; split <;> rename_i h₁
    · have := reverse.termination h₁
      match j with | j+1 => ?_
      simp at *
      rw [(go · (i+1) j)]
      · rwa [Nat.add_right_comm i]
      · simp [size_swap, h₂]
      · intro k
        rw [← getElem?_eq_data_get?, get?_swap]
        simp [getElem?_eq_data_get?, getElem_eq_data_get, ← List.get?_eq_get, H, Nat.le_of_lt h₁]
        split <;> rename_i h₂
        · simp [← h₂, Nat.not_le.2 (Nat.lt_succ_self _)]
          exact (List.get?_reverse' _ _ (Eq.trans (by simp_arith) h)).symm
        split <;> rename_i h₃
        · simp [← h₃, Nat.not_le.2 (Nat.lt_succ_self _)]
          exact (List.get?_reverse' _ _ (Eq.trans (by simp_arith) h)).symm
        simp only [Nat.succ_le, Nat.lt_iff_le_and_ne.trans (and_iff_left h₃),
          Nat.lt_succ.symm.trans (Nat.lt_iff_le_and_ne.trans (and_iff_left (Ne.symm h₂)))]
    · rw [H]; split <;> rename_i h₂
      · cases Nat.le_antisymm (Nat.not_lt.1 h₁) (Nat.le_trans h₂.1 h₂.2)
        cases Nat.le_antisymm h₂.1 h₂.2
        exact (List.get?_reverse' _ _ h).symm
      · rfl
    termination_by j - i
  simp only [reverse]; split
  · match a with | ⟨[]⟩ | ⟨[_]⟩ => rfl
  · have := Nat.sub_add_cancel (Nat.le_of_not_le ‹_›)
    refine List.ext <| go _ _ _ _ (by simp [this]) rfl fun k => ?_
    split; {rfl}; rename_i h
    simp [← show k < _ + 1 ↔ _ from Nat.lt_succ (n := a.size - 1), this] at h
    rw [List.get?_eq_none.2 ‹_›, List.get?_eq_none.2 (a.data.length_reverse ▸ ‹_›)]

theorem forIn_eq_data_forIn [Monad m]
    (as : Array α) (b : β) (f : α → β → m (ForInStep β)) :
    forIn as b f = forIn as.data b f := by
  let rec loop : ∀ {i h b j}, j + i = as.size →
      Array.forIn.loop as f i h b = forIn (as.data.drop j) b f
    | 0, _, _, _, rfl => by rw [List.drop_length]; rfl
    | i+1, _, _, j, ij => by
      simp only [forIn.loop, Nat.add]
      have j_eq : j = size as - 1 - i := by simp [← ij, ← Nat.add_assoc]
      have : as.size - 1 - i < as.size := j_eq ▸ ij ▸ Nat.lt_succ_of_le (Nat.le_add_right ..)
      have : as[size as - 1 - i] :: as.data.drop (j + 1) = as.data.drop j := by
        rw [j_eq]; exact List.get_cons_drop _ ⟨_, this⟩
      simp only [← this, List.forIn_cons]; congr; funext x; congr; funext b
      rw [loop (i := i)]; rw [← ij, Nat.succ_add]; rfl
  conv => lhs; simp only [forIn, Array.forIn]
  rw [loop (Nat.zero_add _)]; rfl

/-! ### foldl / foldr -/

-- This proof is the pure version of `Array.SatisfiesM_foldlM`,
-- reproduced to avoid a dependency on `SatisfiesM`.
theorem foldl_induction
    {as : Array α} (motive : Nat → β → Prop) {init : β} (h0 : motive 0 init) {f : β → α → β}
    (hf : ∀ i : Fin as.size, ∀ b, motive i.1 b → motive (i.1 + 1) (f b as[i])) :
    motive as.size (as.foldl f init) := by
  let rec go {i j b} (h₁ : j ≤ as.size) (h₂ : as.size ≤ i + j) (H : motive j b) :
    (motive as.size) (foldlM.loop (m := Id) f as as.size (Nat.le_refl _) i j b) := by
    unfold foldlM.loop; split
    · next hj =>
      split
      · cases Nat.not_le_of_gt (by simp [hj]) h₂
      · exact go hj (by rwa [Nat.succ_add] at h₂) (hf ⟨j, hj⟩ b H)
    · next hj => exact Nat.le_antisymm h₁ (Nat.ge_of_not_lt hj) ▸ H
  simpa [foldl, foldlM] using go (Nat.zero_le _) (Nat.le_refl _) h0

-- This proof is the pure version of `Array.SatisfiesM_foldrM`,
-- reproduced to avoid a dependency on `SatisfiesM`.
theorem foldr_induction
    {as : Array α} (motive : Nat → β → Prop) {init : β} (h0 : motive as.size init) {f : α → β → β}
    (hf : ∀ i : Fin as.size, ∀ b, motive (i.1 + 1) b → motive i.1 (f as[i] b)) :
    motive 0 (as.foldr f init) := by
  let rec go {i b} (hi : i ≤ as.size) (H : motive i b) :
    (motive 0) (foldrM.fold (m := Id) f as 0 i hi b) := by
    unfold foldrM.fold; simp; split
    · next hi => exact (hi ▸ H)
    · next hi =>
      split; {simp at hi}
      · next i hi' =>
        exact go _ (hf ⟨i, hi'⟩ b H)
  simp [foldr, foldrM]; split; {exact go _ h0}
  · next h => exact (Nat.eq_zero_of_not_pos h ▸ h0)

/-! ### zipWith / zip -/

theorem zipWith_eq_zipWith_data (f : α → β → γ) (as : Array α) (bs : Array β) :
    (as.zipWith bs f).data = as.data.zipWith f bs.data := by
  let rec loop : ∀ (i : Nat) cs, i ≤ as.size → i ≤ bs.size →
      (zipWithAux f as bs i cs).data = cs.data ++ (as.data.drop i).zipWith f (bs.data.drop i) := by
    intro i cs hia hib
    unfold zipWithAux
    by_cases h : i = as.size ∨ i = bs.size
    case pos =>
      have : ¬(i < as.size) ∨ ¬(i < bs.size) := by
        cases h <;> simp_all only [Nat.not_lt, Nat.le_refl, true_or, or_true]
      -- Cleaned up aesop output below
      simp_all only [Nat.not_lt]
      cases h <;> [(cases this); (cases this)]
      · simp_all only [Nat.le_refl, Nat.lt_irrefl, dite_false, List.drop_length,
                      List.zipWith_nil_left, List.append_nil]
      · simp_all only [Nat.le_refl, Nat.lt_irrefl, dite_false, List.drop_length,
                      List.zipWith_nil_left, List.append_nil]
      · simp_all only [Nat.le_refl, Nat.lt_irrefl, dite_false, List.drop_length,
                      List.zipWith_nil_right, List.append_nil]
        split <;> simp_all only [Nat.not_lt]
      · simp_all only [Nat.le_refl, Nat.lt_irrefl, dite_false, List.drop_length,
                      List.zipWith_nil_right, List.append_nil]
        split <;> simp_all only [Nat.not_lt]
    case neg =>
      rw [not_or] at h
      have has : i < as.size := Nat.lt_of_le_of_ne hia h.1
      have hbs : i < bs.size := Nat.lt_of_le_of_ne hib h.2
      simp only [has, hbs, dite_true]
      rw [loop (i+1) _ has hbs, Array.push_data]
      have h₁ : [f as[i] bs[i]] = List.zipWith f [as[i]] [bs[i]] := rfl
      let i_as : Fin as.data.length := ⟨i, has⟩
      let i_bs : Fin bs.data.length := ⟨i, hbs⟩
      rw [h₁, List.append_assoc]
      congr
      rw [← List.zipWith_append (h := by simp), getElem_eq_data_get, getElem_eq_data_get]
      show List.zipWith f ((List.get as.data i_as) :: List.drop (i_as + 1) as.data)
        ((List.get bs.data i_bs) :: List.drop (i_bs + 1) bs.data) =
        List.zipWith f (List.drop i as.data) (List.drop i bs.data)
      simp only [List.get_cons_drop]
    termination_by as.size - i
  simp [zipWith, loop 0 #[] (by simp) (by simp)]

theorem size_zipWith (as : Array α) (bs : Array β) (f : α → β → γ) :
    (as.zipWith bs f).size = min as.size bs.size := by
  rw [size_eq_length_data, zipWith_eq_zipWith_data, List.length_zipWith]

theorem zip_eq_zip_data (as : Array α) (bs : Array β) :
    (as.zip bs).data = as.data.zip bs.data :=
  zipWith_eq_zipWith_data Prod.mk as bs

theorem size_zip (as : Array α) (bs : Array β) :
    (as.zip bs).size = min as.size bs.size :=
  as.size_zipWith bs Prod.mk

/-! ### map -/

@[simp] theorem mem_map {f : α → β} {l : Array α} : b ∈ l.map f ↔ ∃ a, a ∈ l ∧ f a = b := by
  simp only [mem_def, map_data, List.mem_map]

theorem mapM_eq_mapM_data [Monad m] [LawfulMonad m] (f : α → m β) (arr : Array α) :
    arr.mapM f = return mk (← arr.data.mapM f) := by
  rw [mapM_eq_foldlM, foldlM_eq_foldlM_data, ← List.foldrM_reverse]
  conv => rhs; rw [← List.reverse_reverse arr.data]
  induction arr.data.reverse with
  | nil => simp; rfl
  | cons a l ih => simp [ih]; simp [map_eq_pure_bind, push]

theorem mapM_map_eq_foldl (as : Array α) (f : α → β) (i) :
    mapM.map (m := Id) f as i b = as.foldl (start := i) (fun r a => r.push (f a)) b := by
  unfold mapM.map
  split <;> rename_i h
  · simp only [Id.bind_eq]
    dsimp [foldl, Id.run, foldlM]
    rw [mapM_map_eq_foldl, dif_pos (by omega), foldlM.loop, dif_pos h]
    -- Calling `split` here gives a bad goal.
    have : size as - i = Nat.succ (size as - i - 1) := by omega
    rw [this]
    simp [foldl, foldlM, Id.run, Nat.sub_add_eq]
  · dsimp [foldl, Id.run, foldlM]
    rw [dif_pos (by omega), foldlM.loop, dif_neg h]
    rfl
termination_by as.size - i

theorem map_eq_foldl (as : Array α) (f : α → β) :
    as.map f = as.foldl (fun r a => r.push (f a)) #[] :=
  mapM_map_eq_foldl _ _ _

theorem map_induction (as : Array α) (f : α → β) (motive : Nat → Prop) (h0 : motive 0)
    (p : Fin as.size → β → Prop) (hs : ∀ i, motive i.1 → p i (f as[i]) ∧ motive (i+1)) :
    motive as.size ∧
      ∃ eq : (as.map f).size = as.size, ∀ i h, p ⟨i, h⟩ ((as.map f)[i]) := by
  have t := foldl_induction (as := as) (β := Array β)
    (motive := fun i arr => motive i ∧ arr.size = i ∧ ∀ i h2, p i arr[i.1])
    (init := #[]) (f := fun r a => r.push (f a)) ?_ ?_
  obtain ⟨m, eq, w⟩ := t
  · refine ⟨m, by simpa [map_eq_foldl] using eq, ?_⟩
    intro i h
    simp [eq] at w
    specialize w ⟨i, h⟩ trivial
    simpa [map_eq_foldl] using w
  · exact ⟨h0, rfl, nofun⟩
  · intro i b ⟨m, ⟨eq, w⟩⟩
    refine ⟨?_, ?_, ?_⟩
    · exact (hs _ m).2
    · simp_all
    · intro j h
      simp at h ⊢
      by_cases h' : j < size b
      · rw [get_push]
        simp_all
      · rw [get_push, dif_neg h']
        simp only [show j = i by omega]
        exact (hs _ m).1

theorem map_spec (as : Array α) (f : α → β) (p : Fin as.size → β → Prop)
    (hs : ∀ i, p i (f as[i])) :
    ∃ eq : (as.map f).size = as.size, ∀ i h, p ⟨i, h⟩ ((as.map f)[i]) := by
  simpa using map_induction as f (fun _ => True) trivial p (by simp_all)

@[simp] theorem getElem_map (f : α → β) (as : Array α) (i : Nat) (h) :
    ((as.map f)[i]) = f (as[i]'(size_map .. ▸ h)) := by
  have := map_spec as f (fun i b => b = f (as[i]))
  simp only [implies_true, true_implies] at this
  obtain ⟨eq, w⟩ := this
  apply w
  simp_all

/-! ### mapIdx -/

-- This could also be prove from `SatisfiesM_mapIdxM`.
theorem mapIdx_induction (as : Array α) (f : Fin as.size → α → β)
    (motive : Nat → Prop) (h0 : motive 0)
    (p : Fin as.size → β → Prop)
    (hs : ∀ i, motive i.1 → p i (f i as[i]) ∧ motive (i + 1)) :
    motive as.size ∧ ∃ eq : (Array.mapIdx as f).size = as.size,
      ∀ i h, p ⟨i, h⟩ ((Array.mapIdx as f)[i]) := by
  let rec go {bs i j h} (h₁ : j = bs.size) (h₂ : ∀ i h h', p ⟨i, h⟩ bs[i]) (hm : motive j) :
    let arr : Array β := Array.mapIdxM.map (m := Id) as f i j h bs
    motive as.size ∧ ∃ eq : arr.size = as.size, ∀ i h, p ⟨i, h⟩ arr[i] := by
    induction i generalizing j bs with simp [mapIdxM.map]
    | zero =>
      have := (Nat.zero_add _).symm.trans h
      exact ⟨this ▸ hm, h₁ ▸ this, fun _ _ => h₂ ..⟩
    | succ i ih =>
      apply @ih (bs.push (f ⟨j, by omega⟩ as[j])) (j + 1) (by omega) (by simpa using h₁)
      · intro i i_lt h'
        rw [get_push]
        split
        · apply h₂
        · simp only [size_push] at h'
          obtain rfl : i = j := by omega
          apply (hs ⟨i, by omega⟩ hm).1
      · exact (hs ⟨j, by omega⟩ hm).2
  simp [mapIdx, mapIdxM]; exact go rfl nofun h0

theorem mapIdx_spec (as : Array α) (f : Fin as.size → α → β)
    (p : Fin as.size → β → Prop) (hs : ∀ i, p i (f i as[i])) :
    ∃ eq : (Array.mapIdx as f).size = as.size,
      ∀ i h, p ⟨i, h⟩ ((Array.mapIdx as f)[i]) :=
  (mapIdx_induction _ _ (fun _ => True) trivial p fun _ _ => ⟨hs .., trivial⟩).2

@[simp] theorem size_mapIdx (a : Array α) (f : Fin a.size → α → β) : (a.mapIdx f).size = a.size :=
  (mapIdx_spec (p := fun _ _ => True) (hs := fun _ => trivial)).1

@[simp] theorem size_zipWithIndex (as : Array α) : as.zipWithIndex.size = as.size :=
  Array.size_mapIdx _ _

@[simp] theorem getElem_mapIdx (a : Array α) (f : Fin a.size → α → β) (i : Nat)
    (h : i < (mapIdx a f).size) :
    haveI : i < a.size := by simp_all
    (a.mapIdx f)[i] = f ⟨i, this⟩ a[i] :=
  (mapIdx_spec _ _ (fun i b => b = f i a[i]) fun _ => rfl).2 i _

/-! ### modify -/

@[simp] theorem size_modify (a : Array α) (i : Nat) (f : α → α) : (a.modify i f).size = a.size := by
  unfold modify modifyM Id.run
  split <;> simp

theorem get_modify {arr : Array α} {x i} (h : i < arr.size) :
    (arr.modify x f).get ⟨i, by simp [h]⟩ =
    if x = i then f (arr.get ⟨i, h⟩) else arr.get ⟨i, h⟩ := by
  simp [modify, modifyM, Id.run]; split
  · simp [get_set _ _ _ h]; split <;> simp [*]
  · rw [if_neg (mt (by rintro rfl; exact h) ‹_›)]

/-! ### filter -/

@[simp] theorem filter_data (p : α → Bool) (l : Array α) :
    (l.filter p).data = l.data.filter p := by
  dsimp only [filter]
  rw [foldl_eq_foldl_data]
  generalize l.data = l
  suffices ∀ a, (List.foldl (fun r a => if p a = true then push r a else r) a l).data =
      a.data ++ List.filter p l by
    simpa using this #[]
  induction l with simp
  | cons => split <;> simp [*]

@[simp] theorem filter_filter (q) (l : Array α) :
    filter p (filter q l) = filter (fun a => p a ∧ q a) l := by
  apply ext'
  simp only [filter_data, List.filter_filter]

theorem size_filter_le (p : α → Bool) (l : Array α) :
    (l.filter p).size ≤ l.size := by
  simp only [← data_length, filter_data]
  apply List.length_filter_le

@[simp] theorem mem_filter : x ∈ filter p as ↔ x ∈ as ∧ p x := by
  simp only [mem_def, filter_data, List.mem_filter]

theorem mem_of_mem_filter {a : α} {l} (h : a ∈ filter p l) : a ∈ l :=
  (mem_filter.mp h).1

/-! ### filterMap -/

@[simp] theorem filterMap_data (f : α → Option β) (l : Array α) :
    (l.filterMap f).data = l.data.filterMap f := by
  dsimp only [filterMap, filterMapM]
  rw [foldlM_eq_foldlM_data]
  generalize l.data = l
  have this : ∀ a : Array β, (Id.run (List.foldlM (m := Id) ?_ a l)).data =
    a.data ++ List.filterMap f l := ?_
  exact this #[]
  induction l
  · simp_all [Id.run]
  · simp_all [Id.run]
    split <;> simp_all

@[simp] theorem mem_filterMap (f : α → Option β) (l : Array α) {b : β} :
    b ∈ filterMap f l ↔ ∃ a, a ∈ l ∧ f a = some b := by
  simp only [mem_def, filterMap_data, List.mem_filterMap]

/-! ### join -/

@[simp] theorem join_data {l : Array (Array α)} : l.join.data = (l.data.map data).join := by
  dsimp [join]
  simp only [foldl_eq_foldl_data]
  generalize l.data = l
  have : ∀ a : Array α, (List.foldl ?_ a l).data = a.data ++ ?_ := ?_
  exact this #[]
  induction l with
  | nil => simp
  | cons h => induction h.data <;> simp [*]

theorem mem_join : ∀ {L : Array (Array α)}, a ∈ L.join ↔ ∃ l, l ∈ L ∧ a ∈ l := by
  simp only [mem_def, join_data, List.mem_join, List.mem_map]
  intro l
  constructor
  · rintro ⟨_, ⟨s, m, rfl⟩, h⟩
    exact ⟨s, m, h⟩
  · rintro ⟨s, h₁, h₂⟩
    refine ⟨s.data, ⟨⟨s, h₁, rfl⟩, h₂⟩⟩

/-! ### empty -/

theorem size_empty : (#[] : Array α).size = 0 := rfl

theorem empty_data : (#[] : Array α).data = [] := rfl

/-! ### append -/

theorem push_eq_append_singleton (as : Array α) (x) : as.push x = as ++ #[x] := rfl

@[simp] theorem mem_append {a : α} {s t : Array α} : a ∈ s ++ t ↔ a ∈ s ∨ a ∈ t := by
  simp only [mem_def, append_data, List.mem_append]

theorem size_append (as bs : Array α) : (as ++ bs).size = as.size + bs.size := by
  simp only [size, append_data, List.length_append]

theorem get_append_left {as bs : Array α} {h : i < (as ++ bs).size} (hlt : i < as.size) :
    (as ++ bs)[i] = as[i] := by
  simp only [getElem_eq_data_get]
  have h' : i < (as.data ++ bs.data).length := by rwa [← data_length, append_data] at h
  conv => rhs; rw [← List.get_append_left (bs:=bs.data) (h':=h')]
  apply List.get_of_eq; rw [append_data]

theorem get_append_right {as bs : Array α} {h : i < (as ++ bs).size} (hle : as.size ≤ i)
    (hlt : i - as.size < bs.size := Nat.sub_lt_left_of_lt_add hle (size_append .. ▸ h)) :
    (as ++ bs)[i] = bs[i - as.size] := by
  simp only [getElem_eq_data_get]
  have h' : i < (as.data ++ bs.data).length := by rwa [← data_length, append_data] at h
  conv => rhs; rw [← List.get_append_right (h':=h') (h:=Nat.not_lt_of_ge hle)]
  apply List.get_of_eq; rw [append_data]

@[simp] theorem append_nil (as : Array α) : as ++ #[] = as := by
  apply ext'; simp only [append_data, empty_data, List.append_nil]

@[simp] theorem nil_append (as : Array α) : #[] ++ as = as := by
  apply ext'; simp only [append_data, empty_data, List.nil_append]

theorem append_assoc (as bs cs : Array α) : as ++ bs ++ cs = as ++ (bs ++ cs) := by
  apply ext'; simp only [append_data, List.append_assoc]

/-! ### extract -/

theorem extract_loop_zero (as bs : Array α) (start : Nat) : extract.loop as 0 start bs = bs := by
  rw [extract.loop]; split <;> rfl

theorem extract_loop_succ (as bs : Array α) (size start : Nat) (h : start < as.size) :
    extract.loop as (size+1) start bs = extract.loop as size (start+1) (bs.push as[start]) := by
  rw [extract.loop, dif_pos h]; rfl

theorem extract_loop_of_ge (as bs : Array α) (size start : Nat) (h : start ≥ as.size) :
    extract.loop as size start bs = bs := by
  rw [extract.loop, dif_neg (Nat.not_lt_of_ge h)]

theorem extract_loop_eq_aux (as bs : Array α) (size start : Nat) :
    extract.loop as size start bs = bs ++ extract.loop as size start #[] := by
  induction size using Nat.recAux generalizing start bs with
  | zero => rw [extract_loop_zero, extract_loop_zero, append_nil]
  | succ size ih =>
    if h : start < as.size then
      rw [extract_loop_succ (h:=h), ih (bs.push _), push_eq_append_singleton]
      rw [extract_loop_succ (h:=h), ih (#[].push _), push_eq_append_singleton, nil_append]
      rw [append_assoc]
    else
      rw [extract_loop_of_ge (h:=Nat.le_of_not_lt h)]
      rw [extract_loop_of_ge (h:=Nat.le_of_not_lt h)]
      rw [append_nil]

theorem extract_loop_eq (as bs : Array α) (size start : Nat) (h : start + size ≤ as.size) :
  extract.loop as size start bs = bs ++ as.extract start (start + size) := by
  simp [extract]; rw [extract_loop_eq_aux, Nat.min_eq_left h, Nat.add_sub_cancel_left]

theorem size_extract_loop (as bs : Array α) (size start : Nat) :
    (extract.loop as size start bs).size = bs.size + min size (as.size - start) := by
  induction size using Nat.recAux generalizing start bs with
  | zero => rw [extract_loop_zero, Nat.zero_min, Nat.add_zero]
  | succ size ih =>
    if h : start < as.size then
      rw [extract_loop_succ (h:=h), ih, size_push, Nat.add_assoc, ←Nat.add_min_add_left,
        Nat.sub_succ, Nat.one_add, Nat.one_add, Nat.succ_pred_eq_of_pos (Nat.sub_pos_of_lt h)]
    else
      have h := Nat.le_of_not_gt h
      rw [extract_loop_of_ge (h:=h), Nat.sub_eq_zero_of_le h, Nat.min_zero, Nat.add_zero]

@[simp] theorem size_extract (as : Array α) (start stop : Nat) :
    (as.extract start stop).size = min stop as.size - start := by
  simp [extract]; rw [size_extract_loop, size_empty, Nat.zero_add, Nat.sub_min_sub_right,
    Nat.min_assoc, Nat.min_self]

theorem get_extract_loop_lt_aux (as bs : Array α) (size start : Nat) (hlt : i < bs.size) :
    i < (extract.loop as size start bs).size := by
  rw [size_extract_loop]
  apply Nat.lt_of_lt_of_le hlt
  exact Nat.le_add_right ..

theorem get_extract_loop_lt (as bs : Array α) (size start : Nat) (hlt : i < bs.size)
    (h := get_extract_loop_lt_aux as bs size start hlt) :
    (extract.loop as size start bs)[i] = bs[i] := by
  apply Eq.trans _ (get_append_left (bs:=extract.loop as size start #[]) hlt)
  · rw [size_append]; exact Nat.lt_of_lt_of_le hlt (Nat.le_add_right ..)
  · congr; rw [extract_loop_eq_aux]

theorem get_extract_loop_ge_aux (as bs : Array α) (size start : Nat) (hge : i ≥ bs.size)
    (h : i < (extract.loop as size start bs).size) : start + i - bs.size < as.size := by
  have h : i < bs.size + (as.size - start) := by
      apply Nat.lt_of_lt_of_le h
      rw [size_extract_loop]
      apply Nat.add_le_add_left
      exact Nat.min_le_right ..
  rw [Nat.add_sub_assoc hge]
  apply Nat.add_lt_of_lt_sub'
  exact Nat.sub_lt_left_of_lt_add hge h

theorem get_extract_loop_ge (as bs : Array α) (size start : Nat) (hge : i ≥ bs.size)
    (h : i < (extract.loop as size start bs).size)
    (h' := get_extract_loop_ge_aux as bs size start hge h) :
    (extract.loop as size start bs)[i] = as[start + i - bs.size] := by
  induction size using Nat.recAux generalizing start bs with
  | zero =>
    rw [size_extract_loop, Nat.zero_min, Nat.add_zero] at h
    absurd h; exact Nat.not_lt_of_ge hge
  | succ size ih =>
    have : start < as.size := by
      apply Nat.lt_of_le_of_lt (Nat.le_add_right start (i - bs.size))
      rwa [← Nat.add_sub_assoc hge]
    have : i < (extract.loop as size (start+1) (bs.push as[start])).size := by
      rwa [← extract_loop_succ]
    have heq : (extract.loop as (size+1) start bs)[i] =
        (extract.loop as size (start+1) (bs.push as[start]))[i] := by
      congr 1; rw [extract_loop_succ]
    rw [heq]
    if hi : bs.size = i then
      cases hi
      have h₁ : bs.size < (bs.push as[start]).size := by rw [size_push]; exact Nat.lt_succ_self ..
      have h₂ : bs.size < (extract.loop as size (start+1) (bs.push as[start])).size := by
        rw [size_extract_loop]; apply Nat.lt_of_lt_of_le h₁; exact Nat.le_add_right ..
      have h : (extract.loop as size (start + 1) (push bs as[start]))[bs.size] = as[start] := by
        rw [get_extract_loop_lt as (bs.push as[start]) size (start+1) h₁ h₂, get_push_eq]
      rw [h]; congr; rw [Nat.add_sub_cancel]
    else
      have hge : bs.size + 1 ≤ i := Nat.lt_of_le_of_ne hge hi
      rw [ih (bs.push as[start]) (start+1) ((size_push ..).symm ▸ hge)]
      congr 1; rw [size_push, Nat.add_right_comm, Nat.add_sub_add_right]

theorem get_extract_aux {as : Array α} {start stop : Nat} (h : i < (as.extract start stop).size) :
    start + i < as.size := by
  rw [size_extract] at h; apply Nat.add_lt_of_lt_sub'; apply Nat.lt_of_lt_of_le h
  apply Nat.sub_le_sub_right; apply Nat.min_le_right

@[simp] theorem get_extract {as : Array α} {start stop : Nat}
    (h : i < (as.extract start stop).size) :
    (as.extract start stop)[i] = as[start + i]'(get_extract_aux h) :=
  show (extract.loop as (min stop as.size - start) start #[])[i]
    = as[start + i]'(get_extract_aux h) by rw [get_extract_loop_ge]; rfl; exact Nat.zero_le _

@[simp] theorem extract_all (as : Array α) : as.extract 0 as.size = as := by
  apply ext
  · rw [size_extract, Nat.min_self, Nat.sub_zero]
  · intros; rw [get_extract]; congr; rw [Nat.zero_add]

theorem extract_empty_of_stop_le_start (as : Array α) {start stop : Nat} (h : stop ≤ start) :
    as.extract start stop = #[] := by
  simp [extract]; rw [←Nat.sub_min_sub_right, Nat.sub_eq_zero_of_le h, Nat.zero_min,
    extract_loop_zero]

theorem extract_empty_of_size_le_start (as : Array α) {start stop : Nat} (h : as.size ≤ start) :
    as.extract start stop = #[] := by
  simp [extract]; rw [←Nat.sub_min_sub_right, Nat.sub_eq_zero_of_le h, Nat.min_zero,
    extract_loop_zero]

@[simp] theorem extract_empty (start stop : Nat) : (#[] : Array α).extract start stop = #[] :=
  extract_empty_of_size_le_start _ (Nat.zero_le _)

/-! ### any -/

-- Auxiliary for `any_iff_exists`.
theorem anyM_loop_iff_exists (p : α → Bool) (as : Array α) (start stop) (h : stop ≤ as.size) :
    anyM.loop (m := Id) p as stop h start = true ↔
      ∃ i : Fin as.size, start ≤ ↑i ∧ ↑i < stop ∧ p as[i] = true := by
  unfold anyM.loop
  split <;> rename_i h₁
  · dsimp
    split <;> rename_i h₂
    · simp only [true_iff]
      refine ⟨⟨start, by omega⟩, by dsimp; omega, by dsimp; omega, h₂⟩
    · rw [anyM_loop_iff_exists]
      constructor
      · rintro ⟨i, ge, lt, h⟩
        have : start ≠ i := by rintro rfl; omega
        exact ⟨i, by omega, lt, h⟩
      · rintro ⟨i, ge, lt, h⟩
        have : start ≠ i := by rintro rfl; erw [h] at h₂; simp_all
        exact ⟨i, by omega, lt, h⟩
  · simp
    omega
termination_by stop - start

-- This could also be proved from `SatisfiesM_anyM_iff_exists` in `Std.Data.Array.Init.Monadic`
theorem any_iff_exists (p : α → Bool) (as : Array α) (start stop) :
    any as p start stop ↔ ∃ i : Fin as.size, start ≤ i.1 ∧ i.1 < stop ∧ p as[i] := by
  dsimp [any, anyM, Id.run]
  split
  · rw [anyM_loop_iff_exists]; rfl
  · rw [anyM_loop_iff_exists]
    constructor
    · rintro ⟨i, ge, _, h⟩
      exact ⟨i, by omega, by omega, h⟩
    · rintro ⟨i, ge, _, h⟩
      exact ⟨i, by omega, by omega, h⟩

theorem any_eq_true (p : α → Bool) (as : Array α) :
    any as p ↔ ∃ i : Fin as.size, p as[i] := by simp [any_iff_exists, Fin.isLt]

theorem any_def {p : α → Bool} (as : Array α) : as.any p = as.data.any p := by
  rw [Bool.eq_iff_iff, any_eq_true, List.any_eq_true]; simp only [List.mem_iff_get]
  exact ⟨fun ⟨i, h⟩ => ⟨_, ⟨i, rfl⟩, h⟩, fun ⟨_, ⟨i, rfl⟩, h⟩ => ⟨i, h⟩⟩

/-! ### all -/

theorem all_eq_not_any_not (p : α → Bool) (as : Array α) (start stop) :
    all as p start stop = !(any as (!p ·) start stop) := by
  dsimp [all, allM]
  rfl

theorem all_iff_forall (p : α → Bool) (as : Array α) (start stop) :
    all as p start stop ↔ ∀ i : Fin as.size, start ≤ i.1 ∧ i.1 < stop → p as[i] := by
  rw [all_eq_not_any_not]
  suffices ¬(any as (!p ·) start stop = true) ↔
      ∀ i : Fin as.size, start ≤ i.1 ∧ i.1 < stop → p as[i] by
    simp_all
  rw [any_iff_exists]
  simp

theorem all_eq_true (p : α → Bool) (as : Array α) : all as p ↔ ∀ i : Fin as.size, p as[i] := by
  simp [all_iff_forall, Fin.isLt]

theorem all_def {p : α → Bool} (as : Array α) : as.all p = as.data.all p := by
  rw [Bool.eq_iff_iff, all_eq_true, List.all_eq_true]; simp only [List.mem_iff_get]
  constructor
  · rintro w x ⟨r, rfl⟩
    rw [← getElem_eq_data_get]
    apply w
  · intro w i
    exact w as[i] ⟨i, (getElem_eq_data_get as i.2).symm⟩

theorem all_eq_true_iff_forall_mem {l : Array α} : l.all p ↔ ∀ x, x ∈ l → p x := by
  simp only [all_def, List.all_eq_true, mem_def]

/-! ### contains -/

theorem contains_def [DecidableEq α] {a : α} {as : Array α} : as.contains a ↔ a ∈ as := by
  rw [mem_def, contains, any_def, List.any_eq_true]; simp [and_comm]

instance [DecidableEq α] (a : α) (as : Array α) : Decidable (a ∈ as) :=
  decidable_of_iff _ contains_def

/-! ### erase -/

@[simp] proof_wanted erase_data [BEq α] {l : Array α} {a : α} : (l.erase a).data = l.data.erase a

/-! ### swap -/

@[simp] theorem get_swap_right (a : Array α) {i j : Fin a.size} : (a.swap i j)[j.val] = a[i] :=
  by simp only [swap, fin_cast_val, get_eq_getElem, getElem_set_eq, getElem_fin]

@[simp] theorem get_swap_left (a : Array α) {i j : Fin a.size} : (a.swap i j)[i.val] = a[j] :=
  if he : ((Array.size_set _ _ _).symm ▸ j).val = i.val then by
    simp only [←he, fin_cast_val, get_swap_right, getElem_fin]
  else by
    apply Eq.trans
    · apply Array.get_set_ne
      · simp only [size_set, Fin.is_lt]
      · assumption
    · simp [get_set_ne]

@[simp] theorem get_swap_of_ne (a : Array α) {i j : Fin a.size} (hp : p < a.size)
    (hi : p ≠ i) (hj : p ≠ j) : (a.swap i j)[p]'(a.size_swap .. |>.symm ▸ hp) = a[p] := by
  apply Eq.trans
  · have : ((a.size_set i (a.get j)).symm ▸ j).val = j.val := by simp only [fin_cast_val]
    apply Array.get_set_ne
    · simp only [this]
      apply Ne.symm
      · assumption
  · apply Array.get_set_ne
    · apply Ne.symm
      · assumption

theorem get_swap (a : Array α) (i j : Fin a.size) (k : Nat) (hk: k < a.size) :
    (a.swap i j)[k]'(by simp_all) = if k = i then a[j] else if k = j then a[i]  else a[k] := by
  split
  · simp_all only [get_swap_left]
  · split <;> simp_all

theorem get_swap' (a : Array α) (i j : Fin a.size) (k : Nat) (hk' : k < (a.swap i j).size) :
    (a.swap i j)[k] = if k = i then a[j] else if k = j then a[i] else a[k]'(by simp_all) := by
  apply get_swap

@[simp] theorem swap_swap (a : Array α) {i j : Fin a.size} :
    (a.swap i j).swap ⟨i.1, (a.size_swap ..).symm ▸i.2⟩ ⟨j.1, (a.size_swap ..).symm ▸j.2⟩ = a := by
  apply ext
  · simp only [size_swap]
  · intros
    simp only [get_swap']
    split
    · simp_all
    · split <;> simp_all

theorem swap_comm (a : Array α) {i j : Fin a.size} : a.swap i j = a.swap j i := by
  apply ext
  · simp only [size_swap]
  · intros
    simp only [get_swap']
    split
    · split <;> simp_all
    · split <;> simp_all

theorem swap_self (a : Array α) (i : Fin a.size) : a.swap i i = a := by
  apply ext
  · simp only [size_swap]
  · intros
    simp only [get_swap']
    split <;> simp_all

theorem swap_of_append (as : Array α)
  {A a B b C} {i j} (hi : A.length = i.1) (hj : i.1 + B.length + 1 = j.1)
    (eq1 : as.data = A ++ a :: B ++ b :: C) :
    (as.swap i j).data = A ++ b :: B ++ a :: C := by
  simp only [swap, get, data_set, Fin.cast_mk,
    fun a b => show ∀ (e : b = a) (v : Fin b), (e ▸ v) = v.cast e by rintro rfl v; rfl]
  rw [List.get_of_append' (by simpa using eq1) hi]
  rw [List.set_of_append (l₁ := A ++ b :: B) (a := b) (l₂ := C) _ ?_ (by simp [hi, ← hj]; rfl)]
  rw [List.get_of_append' eq1 (by simp [hi, ← hj]; rfl)]
  rw [List.set_of_append (l₁ := A) (a := a) (l₂ := B ++ b :: C) _ (by simp [eq1]) hi]
  simp
