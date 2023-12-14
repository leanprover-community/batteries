/-
Copyright (c) 2021 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Mario Carneiro, Gabriel Ebner
-/
import Std.Data.Nat.Lemmas
import Std.Data.List.Lemmas
import Std.Data.Array.Basic
import Std.Tactic.HaveI
import Std.Tactic.Simpa
import Std.Util.ProofWanted

local macro_rules | `($x[$i]'$h) => `(getElem $x $i $h)

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

namespace Array

attribute [simp] isEmpty uget

@[simp] theorem singleton_def (v : α) : singleton v = #[v] := rfl

@[simp] theorem toArray_data : (a : Array α) → a.data.toArray = a
  | ⟨l⟩ => ext' (data_toArray l)

@[simp] theorem data_length {l : Array α} : l.data.length = l.size := rfl

theorem mem_data {a : α} {l : Array α} : a ∈ l.data ↔ a ∈ l := (mem_def _ _).symm

theorem not_mem_nil (a : α) : ¬ a ∈ #[] := fun.

theorem getElem?_mem {l : Array α} {i : Fin l.size} : l[i] ∈ l := by
  erw [Array.mem_def, getElem_eq_data_get]
  apply List.get_mem

@[simp] theorem get_eq_getElem (a : Array α) (i : Fin _) : a.get i = a[i.1] := rfl
@[simp] theorem get?_eq_getElem? (a : Array α) (i : Nat) : a.get? i = a[i]? := rfl
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

@[simp] theorem getD_eq_get? (a : Array α) (n d) : a.getD n d = (a.get? n).getD d := by
  simp [get?, getD]; split <;> simp

theorem get!_eq_getD [Inhabited α] (a : Array α) : a.get! n = a.getD n default := rfl

@[simp] theorem get!_eq_get? [Inhabited α] (a : Array α) : a.get! n = (a.get? n).getD default := by
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

@[simp] theorem get_set_eq (a : Array α) (i : Fin a.size) (v : α) :
    (a.set i v)[i.1]'(by simp [i.2]) = v := by
  simp only [set, getElem_eq_data_get, List.get_set_eq]

@[simp] theorem get_set_ne (a : Array α) (i : Fin a.size) {j : Nat} (v : α) (hj : j < a.size)
    (h : i.1 ≠ j) : (a.set i v)[j]'(by simp [*]) = a[j] := by
  simp only [set, getElem_eq_data_get, List.get_set_ne h]

@[simp] theorem get?_set_eq (a : Array α) (i : Fin a.size) (v : α) :
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

theorem SatisfiesM_foldrM [Monad m] [LawfulMonad m]
    {as : Array α} (motive : Nat → β → Prop)
    {init : β} (h0 : motive as.size init) {f : α → β → m β}
    (hf : ∀ i : Fin as.size, ∀ b, motive (i.1 + 1) b → SatisfiesM (motive i.1) (f as[i] b)) :
    SatisfiesM (motive 0) (as.foldrM f init) := by
  let rec go {i b} (hi : i ≤ as.size) (H : motive i b) :
    SatisfiesM (motive 0) (foldrM.fold f as 0 i hi b) := by
    unfold foldrM.fold; simp; split
    · next hi => exact .pure (hi ▸ H)
    · next hi =>
      split; {simp at hi}
      · next i hi' =>
        exact (hf ⟨i, hi'⟩ b H).bind fun _ => go _
  simp [foldrM]; split; {exact go _ h0}
  · next h => exact .pure (Nat.eq_zero_of_not_pos h ▸ h0)

theorem foldr_induction
    {as : Array α} (motive : Nat → β → Prop) {init : β} (h0 : motive as.size init) {f : α → β → β}
    (hf : ∀ i : Fin as.size, ∀ b, motive (i.1 + 1) b → motive i.1 (f as[i] b)) :
    motive 0 (as.foldr f init) := by
  have := SatisfiesM_foldrM (m := Id) (as := as) (f := f) motive h0
  simp [SatisfiesM_Id_eq] at this
  exact this hf

theorem mapM_eq_mapM_data [Monad m] [LawfulMonad m] (f : α → m β) (arr : Array α) :
    arr.mapM f = return mk (← arr.data.mapM f) := by
  rw [mapM_eq_foldlM, foldlM_eq_foldlM_data, ← List.foldrM_reverse]
  conv => rhs; rw [← List.reverse_reverse arr.data]
  induction arr.data.reverse with
  | nil => simp; rfl
  | cons a l ih => simp [ih]; simp [map_eq_pure_bind, push]

theorem SatisfiesM_mapIdxM [Monad m] [LawfulMonad m] (as : Array α) (f : Fin as.size → α → m β)
    (motive : Nat → Prop) (h0 : motive 0)
    (p : Fin as.size → β → Prop)
    (hs : ∀ i, motive i.1 → SatisfiesM (p i · ∧ motive (i + 1)) (f i as[i])) :
    SatisfiesM
      (fun arr => motive as.size ∧ ∃ eq : arr.size = as.size, ∀ i h, p ⟨i, h⟩ (arr[i]'(eq ▸ h)))
      (Array.mapIdxM as f) := by
  let rec go {bs i j h} (h₁ : j = bs.size) (h₂ : ∀ i h h', p ⟨i, h⟩ bs[i]) (hm : motive j) :
    SatisfiesM
      (fun arr => motive as.size ∧ ∃ eq : arr.size = as.size, ∀ i h, p ⟨i, h⟩ (arr[i]'(eq ▸ h)))
      (Array.mapIdxM.map as f i j h bs) := by
    induction i generalizing j bs with simp [mapIdxM.map]
    | zero =>
      have := (Nat.zero_add _).symm.trans h
      exact .pure ⟨this ▸ hm, h₁ ▸ this, fun _ _ => h₂ ..⟩
    | succ i ih =>
      refine (hs _ (by exact hm)).bind fun b hb => ih (by simp [h₁]) (fun i hi hi' => ?_) hb.2
      simp at hi'; simp [get_push]; split
      · next h => exact h₂ _ _ h
      · next h => cases h₁.symm ▸ (Nat.le_or_eq_of_le_succ hi').resolve_left h; exact hb.1
  simp [mapIdxM]; exact go rfl (fun.) h0

theorem mapIdx_induction (as : Array α) (f : Fin as.size → α → β)
    (motive : Nat → Prop) (h0 : motive 0)
    (p : Fin as.size → β → Prop)
    (hs : ∀ i, motive i.1 → p i (f i as[i]) ∧ motive (i + 1)) :
    motive as.size ∧ ∃ eq : (Array.mapIdx as f).size = as.size,
      ∀ i h, p ⟨i, h⟩ ((Array.mapIdx as f)[i]'(eq ▸ h)) := by
  have := SatisfiesM_mapIdxM (m := Id) (as := as) (f := f) motive h0
  simp [SatisfiesM_Id_eq] at this
  exact this _ hs

theorem mapIdx_induction' (as : Array α) (f : Fin as.size → α → β)
    (p : Fin as.size → β → Prop) (hs : ∀ i, p i (f i as[i])) :
    ∃ eq : (Array.mapIdx as f).size = as.size,
      ∀ i h, p ⟨i, h⟩ ((Array.mapIdx as f)[i]'(eq ▸ h)) :=
  (mapIdx_induction _ _ (fun _ => True) trivial p fun _ _ => ⟨hs .., trivial⟩).2

@[simp] theorem size_mapIdx (a : Array α) (f : Fin a.size → α → β) : (a.mapIdx f).size = a.size :=
  (mapIdx_induction' (p := fun _ _ => True) (hs := fun _ => trivial)).1

@[simp] theorem getElem_mapIdx (a : Array α) (f : Fin a.size → α → β) (i : Nat) (h) :
    haveI : i < a.size := by simp_all
    (a.mapIdx f)[i]'h = f ⟨i, this⟩ a[i] :=
  (mapIdx_induction' _ _ (fun i b => b = f i a[i]) fun _ => rfl).2 i _

@[simp] theorem size_swap! (a : Array α) (i j) (hi : i < a.size) (hj : j < a.size) :
    (a.swap! i j).size = a.size := by simp [swap!, hi, hj]

@[simp] theorem size_reverse (a : Array α) : a.reverse.size = a.size := by
  let rec go (as : Array α) (i j) : (reverse.loop as i j).size = as.size := by
    rw [reverse.loop]
    if h : i < j then
      have := reverse.termination h
      simp [(go · (i+1) ⟨j-1, ·⟩), h]
    else simp [h]
  simp only [reverse]; split <;> simp [go]
termination_by _ => j - i

@[simp] theorem size_range {n : Nat} : (range n).size = n := by
  unfold range
  induction n with
  | zero      => simp only [Nat.fold, size_toArray, List.length_nil, Nat.zero_eq]
  | succ k ih => simp only [Nat.fold, flip, size_push, ih]

theorem size_modifyM [Monad m] [LawfulMonad m] (a : Array α) (i : Nat) (f : α → m α) :
    SatisfiesM (·.size = a.size) (a.modifyM i f) := by
  unfold modifyM; split
  · exact .bind_pre <| .of_true fun _ => .pure <| by simp only [size_set]
  · exact .pure rfl

@[simp] theorem size_modify (a : Array α) (i : Nat) (f : α → α) : (a.modify i f).size = a.size := by
  rw [← SatisfiesM_Id_eq (p := (·.size = a.size)) (x := a.modify i f)]
  apply size_modifyM

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
  simp only [reverse]; split
  · match a with | ⟨[]⟩ | ⟨[_]⟩ => rfl
  · have := Nat.sub_add_cancel (Nat.le_of_not_le ‹_›)
    refine List.ext <| go _ _ _ _ (by simp [this]) rfl fun k => ?_
    split; {rfl}; rename_i h
    simp [← show k < _ + 1 ↔ _ from Nat.lt_succ (n := a.size - 1), this] at h
    rw [List.get?_eq_none.2 ‹_›, List.get?_eq_none.2 (a.data.length_reverse ▸ ‹_›)]
termination_by _ => j - i

@[simp] theorem size_ofFn_go {n} (f : Fin n → α) (i acc) :
    (ofFn.go f i acc).size = acc.size + (n - i) := by
  if hin : i < n then
    unfold ofFn.go
    have : 1 + (n - (i + 1)) = n - i :=
      Nat.sub_sub .. ▸ Nat.add_sub_cancel' (Nat.le_sub_of_add_le (Nat.add_comm .. ▸ hin))
    rw [dif_pos hin, size_ofFn_go f (i+1), size_push, Nat.add_assoc, this]
  else
    have : n - i = 0 := Nat.sub_eq_zero_of_le (Nat.le_of_not_lt hin)
    unfold ofFn.go
    simp [hin, this]
termination_by _ => n - i

@[simp] theorem size_ofFn (f : Fin n → α) : (ofFn f).size = n := by simp [ofFn]

theorem getElem_ofFn_go (f : Fin n → α) (i) {acc k}
    (hki : k < n) (hin : i ≤ n) (hi : i = acc.size)
    (hacc : ∀ j, ∀ hj : j < acc.size, acc[j] = f ⟨j, Nat.lt_of_lt_of_le hj (hi ▸ hin)⟩) :
    haveI : acc.size + (n - acc.size) = n := Nat.add_sub_cancel' (hi ▸ hin)
    (ofFn.go f i acc)[k]'(by simp [*]) = f ⟨k, hki⟩ := by
  unfold ofFn.go
  if hin : i < n then
    have : 1 + (n - (i + 1)) = n - i :=
      Nat.sub_sub .. ▸ Nat.add_sub_cancel' (Nat.le_sub_of_add_le (Nat.add_comm .. ▸ hin))
    simp only [dif_pos hin]
    rw [getElem_ofFn_go f (i+1) _ hin (by simp [*]) (fun j hj => ?hacc)]
    cases (Nat.lt_or_eq_of_le <| Nat.le_of_lt_succ (by simpa using hj)) with
    | inl hj => simp [get_push, hj, hacc j hj]
    | inr hj => simp [get_push, *]
  else
    simp [hin, hacc k (Nat.lt_of_lt_of_le hki (Nat.le_of_not_lt (hi ▸ hin)))]
termination_by _ => n - i

@[simp] theorem getElem_ofFn (f : Fin n → α) (i : Nat) (h) :
    (ofFn f)[i] = f ⟨i, size_ofFn f ▸ h⟩ :=
  getElem_ofFn_go _ _ _ (by simp) (by simp) fun.

theorem forIn_eq_data_forIn [Monad m]
    (as : Array α) (b : β) (f : α → β → m (ForInStep β)) :
    forIn as b f = forIn as.data b f := by
  let rec loop : ∀ {i h b j}, j + i = as.size →
      Array.forIn.loop as f i h b = forIn (as.data.drop j) b f
    | 0, _, _, _, rfl => by rw [List.drop_length]; rfl
    | i+1, _, _, j, ij => by
      simp [forIn.loop]
      have j_eq : j = size as - 1 - i := by simp [← ij, ← Nat.add_assoc]
      have : as.size - 1 - i < as.size := j_eq ▸ ij ▸ Nat.lt_succ_of_le (Nat.le_add_right ..)
      have : as[size as - 1 - i] :: as.data.drop (j + 1) = as.data.drop j := by
        rw [j_eq]; exact List.get_cons_drop _ ⟨_, this⟩
      simp [← this]; congr; funext x; congr; funext b
      rw [loop (i := i)]; rw [← ij, Nat.succ_add]; rfl
  simp [forIn, Array.forIn]; rw [loop (Nat.zero_add _)]; rfl

/-! ### map -/

@[simp] theorem mem_map {f : α → β} {l : Array α} : b ∈ l.map f ↔ ∃ a, a ∈ l ∧ f a = b := by
  simp only [mem_def, map_data, List.mem_map]

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

/-! ### append -/

@[simp] theorem mem_append {a : α} {s t : Array α} : a ∈ s ++ t ↔ a ∈ s ∨ a ∈ t := by
  simp only [mem_def, append_data, List.mem_append]

/-! ### all -/

theorem all_iff_forall (p : α → Bool) (as : Array α) (start stop) :
    all as p start stop ↔ ∀ i : Fin as.size, start ≤ i.1 ∧ i.1 < stop → p as[i] := by
  have := SatisfiesM_anyM_iff_exists (m := Id) (fun a => ! p a) as start stop (! p as[·]) (by simp)
  rw [SatisfiesM_Id_eq] at this
  dsimp [all, allM, Id.run]
  rw [Bool.not_eq_true', Bool.eq_false_iff, Ne]
  simp [this]

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

/-! ### erase -/

@[simp] proof_wanted erase_data [BEq α] {l : Array α} {a : α} : (l.erase a).data = l.data.erase a
