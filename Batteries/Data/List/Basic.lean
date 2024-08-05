/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Batteries.Data.List.Init.Lemmas
import Batteries.Tactic.Alias

namespace List

/-! ## New definitions -/

/--
Computes the "bag intersection" of `l₁` and `l₂`, that is,
the collection of elements of `l₁` which are also in `l₂`. As each element
is identified, it is removed from `l₂`, so elements are counted with multiplicity.
-/
protected def bagInter {α} [BEq α] : List α → List α → List α
  | [], _ => []
  | _, [] => []
  | a :: l₁, l₂ => if l₂.elem a then a :: List.bagInter l₁ (l₂.erase a) else List.bagInter l₁ l₂

/-- Computes the difference of `l₁` and `l₂`, by removing each element in `l₂` from `l₁`. -/
protected def diff {α} [BEq α] : List α → List α → List α
  | l, [] => l
  | l₁, a :: l₂ => if l₁.elem a then List.diff (l₁.erase a) l₂ else List.diff l₁ l₂

open Option Nat

/-- Get the head and tail of a list, if it is nonempty. -/
@[inline] def next? : List α → Option (α × List α)
  | [] => none
  | a :: l => some (a, l)

/--
Given a function `f : Nat → α → β` and `as : list α`, `as = [a₀, a₁, ...]`, returns the list
`[f 0 a₀, f 1 a₁, ...]`.
-/
@[inline] def mapIdx (f : Nat → α → β) (as : List α) : List β := go as #[] where
  /-- Auxiliary for `mapIdx`:
  `mapIdx.go [a₀, a₁, ...] acc = acc.toList ++ [f acc.size a₀, f (acc.size + 1) a₁, ...]` -/
  @[specialize] go : List α → Array β → List β
  | [], acc => acc.toList
  | a :: as, acc => go as (acc.push (f acc.size a))

/-- Monadic variant of `mapIdx`. -/
@[inline] def mapIdxM {m : Type v → Type w} [Monad m]
    (as : List α) (f : Nat → α → m β) : m (List β) := go as #[] where
  /-- Auxiliary for `mapIdxM`:
  `mapIdxM.go as f acc = acc.toList ++ [← f acc.size a₀, ← f (acc.size + 1) a₁, ...]` -/
  @[specialize] go : List α → Array β → m (List β)
  | [], acc => pure acc.toList
  | a :: as, acc => do go as (acc.push (← f acc.size a))

/--
`after p xs` is the suffix of `xs` after the first element that satisfies
`p`, not including that element.
```lean
after      (· == 1) [0, 1, 2, 3] = [2, 3]
drop_while (· != 1) [0, 1, 2, 3] = [1, 2, 3]
```
-/
@[specialize] def after (p : α → Bool) : List α → List α
  | [] => []
  | x :: xs => bif p x then xs else after p xs

@[deprecated (since := "2024-05-06")] alias removeNth := eraseIdx
@[deprecated (since := "2024-05-06")] alias removeNthTR := eraseIdxTR
@[deprecated (since := "2024-05-06")] alias removeNth_eq_removeNthTR := eraseIdx_eq_eraseIdxTR

/-- Replaces the first element of the list for which `f` returns `some` with the returned value. -/
@[simp] def replaceF (f : α → Option α) : List α → List α
  | [] => []
  | x :: xs => match f x with
    | none => x :: replaceF f xs
    | some a => a :: xs

/-- Tail-recursive version of `replaceF`. -/
@[inline] def replaceFTR (f : α → Option α) (l : List α) : List α := go l #[] where
  /-- Auxiliary for `replaceFTR`: `replaceFTR.go f xs acc = acc.toList ++ replaceF f xs`. -/
  @[specialize] go : List α → Array α → List α
  | [], acc => acc.toList
  | x :: xs, acc => match f x with
    | none => go xs (acc.push x)
    | some a' => acc.toListAppend (a' :: xs)

@[csimp] theorem replaceF_eq_replaceFTR : @replaceF = @replaceFTR := by
  funext α p l; simp [replaceFTR]
  let rec go (acc) : ∀ xs, replaceFTR.go p xs acc = acc.data ++ xs.replaceF p
  | [] => by simp [replaceFTR.go, replaceF]
  | x::xs => by
    simp [replaceFTR.go, replaceF]; cases p x <;> simp
    · rw [go _ xs]; simp
  exact (go #[] _).symm

/--
Constructs the union of two lists, by inserting the elements of `l₁` in reverse order to `l₂`.
As a result, `l₂` will always be a suffix, but only the last occurrence of each element in `l₁`
will be retained (but order will otherwise be preserved).
-/
@[inline] protected def union [BEq α] (l₁ l₂ : List α) : List α := foldr .insert l₂ l₁

instance [BEq α] : Union (List α) := ⟨List.union⟩

/--
Constructs the intersection of two lists, by filtering the elements of `l₁` that are in `l₂`.
Unlike `bagInter` this does not preserve multiplicity: `[1, 1].inter [1]` is `[1, 1]`.
-/
@[inline] protected def inter [BEq α] (l₁ l₂ : List α) : List α := filter (elem · l₂) l₁

instance [BEq α] : Inter (List α) := ⟨List.inter⟩

/--
Split a list at an index.
```
splitAt 2 [a, b, c] = ([a, b], [c])
```
-/
def splitAt (n : Nat) (l : List α) : List α × List α := go l n #[] where
  /-- Auxiliary for `splitAt`: `splitAt.go l n xs acc = (acc.toList ++ take n xs, drop n xs)`
  if `n < length xs`, else `(l, [])`. -/
  go : List α → Nat → Array α → List α × List α
  | [], _, _ => (l, [])
  | x :: xs, n+1, acc => go xs n (acc.push x)
  | xs, _, acc => (acc.toList, xs)

/--
Split a list at an index. Ensures the left list always has the specified length
by right padding with the provided default element.
```
splitAtD 2 [a, b, c] x = ([a, b], [c])
splitAtD 4 [a, b, c] x = ([a, b, c, x], [])
```
-/
def splitAtD (n : Nat) (l : List α) (dflt : α) : List α × List α := go n l #[] where
  /-- Auxiliary for `splitAtD`: `splitAtD.go dflt n l acc = (acc.toList ++ left, right)`
  if `splitAtD n l dflt = (left, right)`. -/
  go : Nat → List α → Array α → List α × List α
  | n+1, x :: xs, acc => go n xs (acc.push x)
  | 0, xs, acc => (acc.toList, xs)
  | n, [], acc => (acc.toListAppend (replicate n dflt), [])

/--
Split a list at every element satisfying a predicate. The separators are not in the result.
```
[1, 1, 2, 3, 2, 4, 4].splitOnP (· == 2) = [[1, 1], [3], [4, 4]]
```
-/
def splitOnP (P : α → Bool) (l : List α) : List (List α) := go l [] where
  /-- Auxiliary for `splitOnP`: `splitOnP.go xs acc = res'`
  where `res'` is obtained from `splitOnP P xs` by prepending `acc.reverse` to the first element. -/
  go : List α → List α → List (List α)
  | [], acc => [acc.reverse]
  | a :: t, acc => if P a then acc.reverse :: go t [] else go t (a::acc)

/-- Tail recursive version of `splitOnP`. -/
@[inline] def splitOnPTR (P : α → Bool) (l : List α) : List (List α) := go l #[] #[] where
  /-- Auxiliary for `splitOnP`: `splitOnP.go xs acc r = r.toList ++ res'`
  where `res'` is obtained from `splitOnP P xs` by prepending `acc.toList` to the first element. -/
  @[specialize] go : List α → Array α → Array (List α) → List (List α)
  | [], acc, r => r.toListAppend [acc.toList]
  | a :: t, acc, r => bif P a then go t #[] (r.push acc.toList) else go t (acc.push a) r

@[csimp] theorem splitOnP_eq_splitOnPTR : @splitOnP = @splitOnPTR := by
  funext α P l; simp [splitOnPTR]
  suffices ∀ xs acc r, splitOnPTR.go P xs acc r = r.data ++ splitOnP.go P xs acc.data.reverse from
    (this l #[] #[]).symm
  intro xs acc r; induction xs generalizing acc r with simp [splitOnP.go, splitOnPTR.go]
  | cons x xs IH => cases P x <;> simp [*]

/--
Split a list at every occurrence of a separator element. The separators are not in the result.
```
[1, 1, 2, 3, 2, 4, 4].splitOn 2 = [[1, 1], [3], [4, 4]]
```
-/
@[inline] def splitOn [BEq α] (a : α) (as : List α) : List (List α) := as.splitOnP (· == a)

/--
Apply a function to the nth tail of `l`. Returns the input without
using `f` if the index is larger than the length of the List.
```
modifyNthTail f 2 [a, b, c] = [a, b] ++ f [c]
```
-/
@[simp] def modifyNthTail (f : List α → List α) : Nat → List α → List α
  | 0, l => f l
  | _+1, [] => []
  | n+1, a :: l => a :: modifyNthTail f n l

/-- Apply `f` to the head of the list, if it exists. -/
@[inline] def modifyHead (f : α → α) : List α → List α
  | [] => []
  | a :: l => f a :: l

@[simp] theorem modifyHead_nil (f : α → α) : [].modifyHead f = [] := by rw [modifyHead]

@[simp] theorem modifyHead_cons (a : α) (l : List α) (f : α → α) :
    (a :: l).modifyHead f = f a :: l := by rw [modifyHead]

/-- Apply `f` to the nth element of the list, if it exists. -/
def modifyNth (f : α → α) : Nat → List α → List α :=
  modifyNthTail (modifyHead f)

/-- Tail-recursive version of `modifyNth`. -/
def modifyNthTR (f : α → α) (n : Nat) (l : List α) : List α := go l n #[] where
  /-- Auxiliary for `modifyNthTR`: `modifyNthTR.go f l n acc = acc.toList ++ modifyNth f n l`. -/
  go : List α → Nat → Array α → List α
  | [], _, acc => acc.toList
  | a :: l, 0, acc => acc.toListAppend (f a :: l)
  | a :: l, n+1, acc => go l n (acc.push a)

theorem modifyNthTR_go_eq : ∀ l n, modifyNthTR.go f l n acc = acc.data ++ modifyNth f n l
  | [], n => by cases n <;> simp [modifyNthTR.go, modifyNth]
  | a :: l, 0 => by simp [modifyNthTR.go, modifyNth]
  | a :: l, n+1 => by simp [modifyNthTR.go, modifyNth, modifyNthTR_go_eq l]

@[csimp] theorem modifyNth_eq_modifyNthTR : @modifyNth = @modifyNthTR := by
  funext α f n l; simp [modifyNthTR, modifyNthTR_go_eq]

/-- Apply `f` to the last element of `l`, if it exists. -/
@[inline] def modifyLast (f : α → α) (l : List α) : List α := go l #[] where
  /-- Auxiliary for `modifyLast`: `modifyLast.go f l acc = acc.toList ++ modifyLast f l`. -/
  @[specialize] go : List α → Array α → List α
  | [], _ => []
  | [x], acc => acc.toListAppend [f x]
  | x :: xs, acc => go xs (acc.push x)

/--
`insertNth n a l` inserts `a` into the list `l` after the first `n` elements of `l`
```
insertNth 2 1 [1, 2, 3, 4] = [1, 2, 1, 3, 4]
```
-/
def insertNth (n : Nat) (a : α) : List α → List α :=
  modifyNthTail (cons a) n

/-- Tail-recursive version of `insertNth`. -/
@[inline] def insertNthTR (n : Nat) (a : α) (l : List α) : List α := go n l #[] where
  /-- Auxiliary for `insertNthTR`: `insertNthTR.go a n l acc = acc.toList ++ insertNth n a l`. -/
  go : Nat → List α → Array α → List α
  | 0, l, acc => acc.toListAppend (a :: l)
  | _, [], acc => acc.toList
  | n+1, a :: l, acc => go n l (acc.push a)

theorem insertNthTR_go_eq : ∀ n l, insertNthTR.go a n l acc = acc.data ++ insertNth n a l
  | 0, l | _+1, [] => by simp [insertNthTR.go, insertNth]
  | n+1, a :: l => by simp [insertNthTR.go, insertNth, insertNthTR_go_eq n l]

@[csimp] theorem insertNth_eq_insertNthTR : @insertNth = @insertNthTR := by
  funext α f n l; simp [insertNthTR, insertNthTR_go_eq]

theorem headD_eq_head? (l) (a : α) : headD l a = (head? l).getD a := by cases l <;> rfl

/--
Take `n` elements from a list `l`. If `l` has less than `n` elements, append `n - length l`
elements `x`.
-/
def takeD : Nat → List α → α → List α
  | 0, _, _ => []
  | n+1, l, x => l.headD x :: takeD n l.tail x

@[simp] theorem takeD_zero (l) (a : α) : takeD 0 l a = [] := rfl
@[simp] theorem takeD_succ (l) (a : α) :
    takeD (n+1) l a = l.head?.getD a :: takeD n l.tail a := by simp [takeD]

@[simp] theorem takeD_nil (n) (a : α) : takeD n [] a = replicate n a := by
  induction n <;> simp [*, replicate_succ]

/-- Tail-recursive version of `takeD`. -/
def takeDTR (n : Nat) (l : List α) (dflt : α) : List α := go n l #[] where
  /-- Auxiliary for `takeDTR`: `takeDTR.go dflt n l acc = acc.toList ++ takeD n l dflt`. -/
  go : Nat → List α → Array α → List α
  | n+1, x :: xs, acc => go n xs (acc.push x)
  | 0, _, acc => acc.toList
  | n, [], acc => acc.toListAppend (replicate n dflt)

theorem takeDTR_go_eq : ∀ n l, takeDTR.go dflt n l acc = acc.data ++ takeD n l dflt
  | 0, _ => by simp [takeDTR.go]
  | _+1, [] => by simp [takeDTR.go, replicate_succ]
  | _+1, _::l => by simp [takeDTR.go, takeDTR_go_eq _ l]

@[csimp] theorem takeD_eq_takeDTR : @takeD = @takeDTR := by
  funext α f n l; simp [takeDTR, takeDTR_go_eq]

/--
Fold a function `f` over the list from the left, returning the list of partial results.
```
scanl (+) 0 [1, 2, 3] = [0, 1, 3, 6]
```
-/
@[simp] def scanl (f : α → β → α) (a : α) : List β → List α
  | [] => [a]
  | b :: l => a :: scanl f (f a b) l

/-- Tail-recursive version of `scanl`. -/
@[inline] def scanlTR (f : α → β → α) (a : α) (l : List β) : List α := go l a #[] where
  /-- Auxiliary for `scanlTR`: `scanlTR.go f l a acc = acc.toList ++ scanl f a l`. -/
  @[specialize] go : List β → α → Array α → List α
  | [], a, acc => acc.toListAppend [a]
  | b :: l, a, acc => go l (f a b) (acc.push a)

theorem scanlTR_go_eq : ∀ l, scanlTR.go f l a acc = acc.data ++ scanl f a l
  | [] => by simp [scanlTR.go, scanl]
  | a :: l => by simp [scanlTR.go, scanl, scanlTR_go_eq l]

@[csimp] theorem scanl_eq_scanlTR : @scanl = @scanlTR := by
  funext α f n l; simp (config := { unfoldPartialApp := true }) [scanlTR, scanlTR_go_eq]

/--
Fold a function `f` over the list from the right, returning the list of partial results.
```
scanr (+) 0 [1, 2, 3] = [6, 5, 3, 0]
```
-/
def scanr (f : α → β → β) (b : β) (l : List α) : List β :=
  let (b', l') := l.foldr (fun a (b', l') => (f a b', b' :: l')) (b, [])
  b' :: l'

/--
Fold a list from left to right as with `foldl`, but the combining function
also receives each element's index.
-/
@[simp, specialize] def foldlIdx (f : Nat → α → β → α) (init : α) : List β → (start : _ := 0) → α
  | [], _ => init
  | b :: l, i => foldlIdx f (f i init b) l (i+1)

/--
Fold a list from right to left as with `foldr`, but the combining function
also receives each element's index.
-/
-- TODO(Mario): tail recursive / array-based implementation
@[simp, specialize] def foldrIdx (f : Nat → α → β → β) (init : β) :
    (l : List α) → (start : _ := 0) → β
  | [], _ => init
  | a :: l, i => f i a (foldrIdx f init l (i+1))

/-- `findIdxs p l` is the list of indexes of elements of `l` that satisfy `p`. -/
@[inline] def findIdxs (p : α → Bool) (l : List α) : List Nat :=
  foldrIdx (fun i a is => if p a then i :: is else is) [] l

/--
Returns the elements of `l` that satisfy `p` together with their indexes in
`l`. The returned list is ordered by index.
-/
@[inline] def indexesValues (p : α → Bool) (l : List α) : List (Nat × α) :=
  foldrIdx (fun i a l => if p a then (i, a) :: l else l) [] l

/--
`indexesOf a l` is the list of all indexes of `a` in `l`. For example:
```
indexesOf a [a, b, a, a] = [0, 2, 3]
```
-/
@[inline] def indexesOf [BEq α] (a : α) : List α → List Nat := findIdxs (· == a)

/--
`lookmap` is a combination of `lookup` and `filterMap`.
`lookmap f l` will apply `f : α → Option α` to each element of the list,
replacing `a → b` at the first value `a` in the list such that `f a = some b`.
-/
@[inline] def lookmap (f : α → Option α) (l : List α) : List α := go l #[] where
  /-- Auxiliary for `lookmap`: `lookmap.go f l acc = acc.toList ++ lookmap f l`. -/
  @[specialize] go : List α → Array α → List α
  | [], acc => acc.toList
  | a :: l, acc => match f a with
    | some b => acc.toListAppend (b :: l)
    | none => go l (acc.push a)

/--
`inits l` is the list of initial segments of `l`.
```
inits [1, 2, 3] = [[], [1], [1, 2], [1, 2, 3]]
```
-/
@[simp] def inits : List α → List (List α)
  | [] => [[]]
  | a :: l => [] :: map (fun t => a :: t) (inits l)

/-- Tail-recursive version of `inits`. -/
def initsTR (l : List α) : List (List α) :=
  l.foldr (fun a arrs => (arrs.map fun t => a :: t).push []) #[[]] |>.toListRev

@[csimp] theorem inits_eq_initsTR : @inits = @initsTR := by
  funext α l; simp [initsTR]; induction l <;> simp [*, map_reverse]

/--
`tails l` is the list of terminal segments of `l`.
```
tails [1, 2, 3] = [[1, 2, 3], [2, 3], [3], []]
```
-/
@[simp] def tails : List α → List (List α)
  | [] => [[]]
  | a :: l => (a :: l) :: tails l

/-- Tail-recursive version of `tails`. -/
def tailsTR (l : List α) : List (List α) := go l #[] where
  /-- Auxiliary for `tailsTR`: `tailsTR.go l acc = acc.toList ++ tails l`. -/
  go (l : List α) (acc : Array (List α)) : List (List α) :=
    match l with
    | [] => acc.toListAppend [[]]
    | _::xs => go xs (acc.push l)

@[csimp] theorem tails_eq_tailsTR : @tails = @tailsTR := by
  funext α
  have H (l : List α) : ∀ acc, tailsTR.go l acc = acc.toList ++ tails l := by
    induction l <;> simp [*, tailsTR.go]
  simp (config := { unfoldPartialApp := true }) [tailsTR, H]

/--
`sublists' l` is the list of all (non-contiguous) sublists of `l`.
It differs from `sublists` only in the order of appearance of the sublists;
`sublists'` uses the first element of the list as the MSB,
`sublists` uses the first element of the list as the LSB.
```
sublists' [1, 2, 3] = [[], [3], [2], [2, 3], [1], [1, 3], [1, 2], [1, 2, 3]]
```
-/
def sublists' (l : List α) : List (List α) :=
  let f a arr := arr.foldl (init := arr) fun r l => r.push (a :: l)
  (l.foldr f #[[]]).toList

/--
`sublists l` is the list of all (non-contiguous) sublists of `l`; cf. `sublists'`
for a different ordering.
```
sublists [1, 2, 3] = [[], [1], [2], [1, 2], [3], [1, 3], [2, 3], [1, 2, 3]]
```
-/
def sublists (l : List α) : List (List α) :=
  l.foldr (fun a acc => acc.bind fun x => [x, a :: x]) [[]]

/-- A version of `List.sublists` that has faster runtime performance but worse kernel performance -/
def sublistsFast (l : List α) : List (List α) :=
  let f a arr := arr.foldl (init := Array.mkEmpty (arr.size * 2))
    fun r l => (r.push l).push (a :: l)
  (l.foldr f #[[]]).toList

-- The fact that this transformation is safe is proved in mathlib4 as `sublists_eq_sublistsFast`.
-- Using a `csimp` lemma here is impractical as we are missing a lot of lemmas about lists.
-- TODO(batteries#307): upstream the necessary results about `sublists` and put the `csimp` lemma in
-- `Batteries/Data/List/Lemmas.lean`.
attribute [implemented_by sublistsFast] sublists

section Forall₂

variable {r : α → β → Prop} {p : γ → δ → Prop}

/--
`Forall₂ R l₁ l₂` means that `l₁` and `l₂` have the same length,
and whenever `a` is the nth element of `l₁`, and `b` is the nth element of `l₂`,
then `R a b` is satisfied.
-/
inductive Forall₂ (R : α → β → Prop) : List α → List β → Prop
  /-- Two nil lists are `Forall₂`-related -/
  | nil : Forall₂ R [] []
  /-- Two cons lists are related by `Forall₂ R`
  if the heads are related by `R` and the tails are related by `Forall₂ R` -/
  | cons {a b l₁ l₂} : R a b → Forall₂ R l₁ l₂ → Forall₂ R (a :: l₁) (b :: l₂)

attribute [simp] Forall₂.nil

@[simp] theorem forall₂_cons {R : α → β → Prop} {a b l₁ l₂} :
    Forall₂ R (a :: l₁) (b :: l₂) ↔ R a b ∧ Forall₂ R l₁ l₂ :=
  ⟨fun | .cons h tail => ⟨h, tail⟩, fun ⟨head, tail⟩ => .cons head tail⟩

/--
Check for all elements `a`, `b`, where `a` and `b` are the nth element of the first and second
List respectively, that `r a b = true`.
-/
def all₂ (r : α → β → Bool) : List α → List β → Bool
  | [], [] => true
  | a::as, b::bs =>
    if r a b then
      all₂ r as bs
    else false
  | _, _ => false

@[simp] theorem all₂_eq_true {r : α → β → Bool} :
    ∀ l₁ l₂, all₂ r l₁ l₂ ↔ Forall₂ (r · ·) l₁ l₂
  | [], [] => by simp [all₂]
  | a::as, b::bs => by
    by_cases h : r a b
      <;> simp [all₂, h, all₂_eq_true, forall₂_cons]
  | _::_, [] | [], _::_ => by
    simp [all₂]
    exact nofun

instance {R : α → β → Prop} [∀ a b, Decidable (R a b)] : ∀ l₁ l₂, Decidable (Forall₂ R l₁ l₂) :=
  fun l₁ l₂ => decidable_of_iff (all₂ (R · ·) l₁ l₂) (by simp [all₂_eq_true])

end Forall₂

/--
Transpose of a list of lists, treated as a matrix.
```
transpose [[1, 2], [3, 4], [5, 6]] = [[1, 3, 5], [2, 4, 6]]
```
-/
def transpose (l : List (List α)) : List (List α) := (l.foldr go #[]).toList where
  /-- `pop : List α → StateM (List α) (List α)` transforms the input list `old`
  by taking the head of the current state and pushing it on the head of `old`.
  If the state list is empty, then `old` is left unchanged. -/
  pop (old : List α) : StateM (List α) (List α)
    | [] => (old, [])
    | a :: l => (a :: old, l)

  /-- `go : List α → Array (List α) → Array (List α)` handles the insertion of
  a new list into all the lists in the array:
  `go [a, b, c] #[l₁, l₂, l₃] = #[a::l₁, b::l₂, c::l₃]`.
  If the new list is too short, the later lists are unchanged, and if it is too long
  the array is extended:
  ```
  go [a] #[l₁, l₂, l₃] = #[a::l₁, l₂, l₃]
  go [a, b, c, d] #[l₁, l₂, l₃] = #[a::l₁, b::l₂, c::l₃, [d]]
  ```
  -/
  go (l : List α) (acc : Array (List α)) : Array (List α) :=
    let (acc, l) := acc.mapM pop l
    l.foldl (init := acc) fun arr a => arr.push [a]

/--
List of all sections through a list of lists. A section
of `[L₁, L₂, ..., Lₙ]` is a list whose first element comes from
`L₁`, whose second element comes from `L₂`, and so on.
-/
@[simp] def sections : List (List α) → List (List α)
  | [] => [[]]
  | l :: L => (sections L).bind fun s => l.map fun a => a :: s

/-- Optimized version of `sections`. -/
def sectionsTR (L : List (List α)) : List (List α) :=
  bif L.any isEmpty then [] else (L.foldr go #[[]]).toList
where
  /-- `go : List α → Array (List α) → Array (List α)` inserts one list into the accumulated
  list of sections `acc`: `go [a, b] #[l₁, l₂] = [a::l₁, b::l₁, a::l₂, b::l₂]`. -/
  go (l : List α) (acc : Array (List α)) : Array (List α) :=
    acc.foldl (init := #[]) fun acc' l' =>
      l.foldl (init := acc') fun acc' a =>
        acc'.push (a :: l')

theorem sections_eq_nil_of_isEmpty : ∀ {L}, L.any isEmpty → @sections α L = []
  | l :: L, h => by
    simp only [any, foldr, Bool.or_eq_true] at h
    match l, h with
    | [], .inl rfl => simp; induction sections L <;> simp [*]
    | l, .inr h => simp [sections, sections_eq_nil_of_isEmpty h]

@[csimp] theorem sections_eq_sectionsTR : @sections = @sectionsTR := by
  funext α L; simp [sectionsTR]
  cases e : L.any isEmpty <;> simp [sections_eq_nil_of_isEmpty, *]
  clear e; induction L with | nil => rfl | cons l L IH => ?_
  simp [IH, sectionsTR.go]
  rw [Array.foldl_eq_foldl_data, Array.foldl_data_eq_bind]; rfl
  intros; apply Array.foldl_data_eq_map

/--
`extractP p l` returns a pair of an element `a` of `l` satisfying the predicate
`p`, and `l`, with `a` removed. If there is no such element `a` it returns `(none, l)`.
-/
def extractP (p : α → Bool) (l : List α) : Option α × List α := go l #[] where
  /-- Auxiliary for `extractP`:
  `extractP.go p l xs acc = (some a, acc.toList ++ out)` if `extractP p xs = (some a, out)`,
  and `extractP.go p l xs acc = (none, l)` if `extractP p xs = (none, _)`. -/
  go : List α → Array α → Option α × List α
  | [], _ => (none, l)
  | a :: l, acc => bif p a then (some a, acc.toListAppend l) else go l (acc.push a)

/--
`revzip l` returns a list of pairs of the elements of `l` paired
with the elements of `l` in reverse order.
```
revzip [1, 2, 3, 4, 5] = [(1, 5), (2, 4), (3, 3), (4, 2), (5, 1)]
```
-/
def revzip (l : List α) : List (α × α) := zip l l.reverse

/--
`product l₁ l₂` is the list of pairs `(a, b)` where `a ∈ l₁` and `b ∈ l₂`.
```
product [1, 2] [5, 6] = [(1, 5), (1, 6), (2, 5), (2, 6)]
```
-/
def product (l₁ : List α) (l₂ : List β) : List (α × β) := l₁.bind fun a => l₂.map (Prod.mk a)

/-- Optimized version of `product`. -/
def productTR (l₁ : List α) (l₂ : List β) : List (α × β) :=
  l₁.foldl (fun acc a => l₂.foldl (fun acc b => acc.push (a, b)) acc) #[] |>.toList

@[csimp] theorem product_eq_productTR : @product = @productTR := by
  funext α β l₁ l₂; simp [product, productTR]
  rw [Array.foldl_data_eq_bind]; rfl
  intros; apply Array.foldl_data_eq_map

/-- `sigma l₁ l₂` is the list of dependent pairs `(a, b)` where `a ∈ l₁` and `b ∈ l₂ a`.
```
sigma [1, 2] (λ_, [(5 : Nat), 6]) = [(1, 5), (1, 6), (2, 5), (2, 6)]
``` -/
protected def sigma {σ : α → Type _} (l₁ : List α) (l₂ : ∀ a, List (σ a)) : List (Σ a, σ a) :=
  l₁.bind fun a => (l₂ a).map (Sigma.mk a)

/-- Optimized version of `sigma`. -/
def sigmaTR {σ : α → Type _} (l₁ : List α) (l₂ : ∀ a, List (σ a)) : List (Σ a, σ a) :=
  l₁.foldl (fun acc a => (l₂ a).foldl (fun acc b => acc.push ⟨a, b⟩) acc) #[] |>.toList

@[csimp] theorem sigma_eq_sigmaTR : @List.sigma = @sigmaTR := by
  funext α β l₁ l₂; simp [List.sigma, sigmaTR]
  rw [Array.foldl_data_eq_bind]; rfl
  intros; apply Array.foldl_data_eq_map

/--
`ofFn f` with `f : fin n → α` returns the list whose ith element is `f i`
```
ofFn f = [f 0, f 1, ... , f (n - 1)]
```
-/
def ofFn {n} (f : Fin n → α) : List α := go n 0 rfl where
  /-- Auxiliary for `List.ofFn`. `ofFn.go f i j _ = [f j, ..., f (n - 1)]`. -/
  -- This used to be defined via `Array.ofFn` but mathlib relies on reducing it,
  -- so we use a structurally recursive definition here.
  go : (i j : Nat) → (h : i + j = n) → List α
  | 0, _, _ => []
  | i+1, j, h => f ⟨j, by omega⟩ :: go i (j+1) (Nat.add_right_comm .. ▸ h :)

/-- Tail-recursive version of `ofFn`. -/
@[inline] def ofFnTR {n} (f : Fin n → α) : List α := go n (Nat.le_refl _) [] where
  /-- Auxiliary for `List.ofFnTR`. `ofFnTR.go f i _ acc = f 0 :: ... :: f (i - 1) :: acc`. -/
  go : (i : Nat) → (h : i ≤ n) → List α → List α
  | 0, _, acc => acc
  | i+1, h, acc => go i (Nat.le_of_lt h) (f ⟨i, h⟩ :: acc)

@[csimp] theorem ofFn_eq_ofFnTR : @ofFn = @ofFnTR := by
  funext α n f; simp [ofFnTR]
  let rec go (i j h h') : ofFnTR.go f j h' (ofFn.go f i j h) = ofFn f := by
    unfold ofFnTR.go; split
    · subst h; rfl
    · next l j h' => exact go (i+1) j ((Nat.succ_add ..).trans h) (Nat.le_of_lt h')
  exact (go 0 n (Nat.zero_add _) (Nat.le_refl _)).symm

/-- `ofFnNthVal f i` returns `some (f i)` if `i < n` and `none` otherwise. -/
def ofFnNthVal {n} (f : Fin n → α) (i : Nat) : Option α :=
  if h : i < n then some (f ⟨i, h⟩) else none

/-- `disjoint l₁ l₂` means that `l₁` and `l₂` have no elements in common. -/
def Disjoint (l₁ l₂ : List α) : Prop :=
  ∀ ⦃a⦄, a ∈ l₁ → a ∈ l₂ → False

/--
Returns the longest initial prefix of two lists such that they are pairwise related by `R`.
```
takeWhile₂ (· < ·) [1, 2, 4, 5] [5, 4, 3, 6] = ([1, 2], [5, 4])
```
-/
def takeWhile₂ (R : α → β → Bool) : List α → List β → List α × List β
  | a::as, b::bs => if R a b then
      let (as', bs') := takeWhile₂ R as bs
      (a::as', b::bs')
    else ([], [])
  | _, _ => ([], [])

/-- Tail-recursive version of `takeWhile₂`. -/
@[inline] def takeWhile₂TR (R : α → β → Bool) (as : List α) (bs : List β) : List α × List β :=
  go as bs [] []
where
  /-- Auxiliary for `takeWhile₂TR`:
  `takeWhile₂TR.go R as bs acca accb = (acca.reverse ++ as', acca.reverse ++ bs')`
  if `takeWhile₂ R as bs = (as', bs')`. -/
  @[specialize] go : List α → List β → List α → List β → List α × List β
  | a::as, b::bs, acca, accb =>
    bif R a b then go as bs (a::acca) (b::accb) else (acca.reverse, accb.reverse)
  | _, _, acca, accb => (acca.reverse, accb.reverse)

@[csimp] theorem takeWhile₂_eq_takeWhile₂TR : @takeWhile₂ = @takeWhile₂TR := by
  funext α β R as bs; simp [takeWhile₂TR]
  let rec go (as bs acca accb) : takeWhile₂TR.go R as bs acca accb =
      (acca.reverse ++ (as.takeWhile₂ R bs).1, accb.reverse ++ (as.takeWhile₂ R bs).2) := by
    unfold takeWhile₂TR.go takeWhile₂; split <;> simp
    rename_i a as b bs; unfold cond; cases R a b <;> simp [go as bs]
  exact (go as bs [] []).symm

/--
`pwFilter R l` is a maximal sublist of `l` which is `Pairwise R`.
`pwFilter (·≠·)` is the erase duplicates function (cf. `eraseDup`), and `pwFilter (·<·)` finds
a maximal increasing subsequence in `l`. For example,
```
pwFilter (·<·) [0, 1, 5, 2, 6, 3, 4] = [0, 1, 2, 3, 4]
```
-/
def pwFilter (R : α → α → Prop) [DecidableRel R] (l : List α) : List α :=
  l.foldr (fun x IH => if ∀ y ∈ IH, R x y then x :: IH else IH) []

section Chain

variable (R : α → α → Prop)

/-- `Chain R a l` means that `R` holds between adjacent elements of `a::l`.
```
Chain R a [b, c, d] ↔ R a b ∧ R b c ∧ R c d
``` -/
inductive Chain : α → List α → Prop
  /-- A chain of length 1 is trivially a chain. -/
  | nil {a : α} : Chain a []
  /-- If `a` relates to `b` and `b::l` is a chain, then `a :: b :: l` is also a chain. -/
  | cons : ∀ {a b : α} {l : List α}, R a b → Chain b l → Chain a (b :: l)

/-- `Chain' R l` means that `R` holds between adjacent elements of `l`.
```
Chain' R [a, b, c, d] ↔ R a b ∧ R b c ∧ R c d
``` -/
def Chain' : List α → Prop
  | [] => True
  | a :: l => Chain R a l

end Chain

/-- `eraseDup l` removes duplicates from `l` (taking only the first occurrence).
Defined as `pwFilter (≠)`.

    eraseDup [1, 0, 2, 2, 1] = [0, 2, 1] -/
@[inline] def eraseDup [BEq α] : List α → List α := pwFilter (· != ·)

/--
`ilast' x xs` returns the last element of `xs` if `xs` is non-empty; it returns `x` otherwise.
Use `List.getLastD` instead.
-/
@[simp, deprecated getLastD (since := "2024-01-09")] def ilast' {α} : α → List α → α
  | a, [] => a
  | _, b :: l => ilast' b l

/--
`last' xs` returns the last element of `xs` if `xs` is non-empty; it returns `none` otherwise.
Use `List.getLast?` instead
-/
@[simp, deprecated getLast? (since := "2024-01-09")] def last' {α} : List α → Option α
  | [] => none
  | [a] => some a
  | _ :: l => last' l

/--
`rotate l n` rotates the elements of `l` to the left by `n`
```
rotate [0, 1, 2, 3, 4, 5] 2 = [2, 3, 4, 5, 0, 1]
```
-/
@[inline] def rotate (l : List α) (n : Nat) : List α :=
  let (l₁, l₂) := List.splitAt (n % l.length) l
  l₂ ++ l₁

/-- `rotate'` is the same as `rotate`, but slower. Used for proofs about `rotate` -/
@[simp] def rotate' : List α → Nat → List α
  | [], _ => []
  | l, 0 => l
  | a :: l, n+1 => rotate' (l ++ [a]) n

/--
`mapDiagM f l` calls `f` on all elements in the upper triangular part of `l × l`.
That is, for each `e ∈ l`, it will run `f e e` and then `f e e'`
for each `e'` that appears after `e` in `l`.
```
mapDiagM f [1, 2, 3] =
  return [← f 1 1, ← f 1 2, ← f 1 3, ← f 2 2, ← f 2 3, ← f 3 3]
```
-/
def mapDiagM [Monad m] (f : α → α → m β) (l : List α) : m (List β) := go l #[] where
  /-- Auxiliary for `mapDiagM`: `mapDiagM.go as f acc = (acc.toList ++ ·) <$> mapDiagM f as` -/
  go : List α → Array β → m (List β)
  | [], acc => pure acc.toList
  | x::xs, acc => do
    let b ← f x x
    let acc ← xs.foldlM (·.push <$> f x ·) (acc.push b)
    go xs acc

/--
`forDiagM f l` calls `f` on all elements in the upper triangular part of `l × l`.
That is, for each `e ∈ l`, it will run `f e e` and then `f e e'`
for each `e'` that appears after `e` in `l`.
```
forDiagM f [1, 2, 3] = do f 1 1; f 1 2; f 1 3; f 2 2; f 2 3; f 3 3
```
-/
@[simp] def forDiagM [Monad m] (f : α → α → m PUnit) : List α → m PUnit
  | [] => pure ⟨⟩
  | x :: xs => do f x x; xs.forM (f x); xs.forDiagM f

/-- `getRest l l₁` returns `some l₂` if `l = l₁ ++ l₂`.
  If `l₁` is not a prefix of `l`, returns `none` -/
def getRest [DecidableEq α] : List α → List α → Option (List α)
  | l, [] => some l
  | [], _ => none
  | x :: l, y :: l₁ => if x = y then getRest l l₁ else none

/-- `List.dropSlice n m xs` removes a slice of length `m` at index `n` in list `xs`. -/
@[simp] def dropSlice : Nat → Nat → List α → List α
  | _, _, [] => []
  | 0, m, xs => xs.drop m
  | n+1, m, x :: xs => x :: dropSlice n m xs

/-- Optimized version of `dropSlice`. -/
@[inline] def dropSliceTR (n m : Nat) (l : List α) : List α :=
  match m with
  | 0 => l
  | m+1 => go m l n #[]
where
  /-- Auxiliary for `dropSliceTR`: `dropSliceTR.go l m xs n acc = acc.toList ++ dropSlice n m xs`
  unless `n ≥ length xs`, in which case it is `l`. -/
  go (m : Nat) : List α → Nat → Array α → List α
  | [],    _,   _   => l
  | _::xs, 0,   acc => acc.toListAppend (xs.drop m)
  | x::xs, n+1, acc => go m xs n (acc.push x)

theorem dropSlice_zero₂ : ∀ n l, @dropSlice α n 0 l = l
  | 0, [] | 0, _::_ | n+1, [] => rfl
  | n+1, x::xs => by simp [dropSlice, dropSlice_zero₂]

@[csimp] theorem dropSlice_eq_dropSliceTR : @dropSlice = @dropSliceTR := by
  funext α n m l; simp [dropSliceTR]
  split; { rw [dropSlice_zero₂] }
  rename_i m
  let rec go (acc) : ∀ xs n, l = acc.data ++ xs →
    dropSliceTR.go l m xs n acc = acc.data ++ xs.dropSlice n (m+1)
  | [],    n
  | _::xs, 0 => fun h => by simp [dropSliceTR.go, dropSlice, h]
  | x::xs, n+1 => by simp [dropSliceTR.go, dropSlice]; intro h; rw [go _ xs]; {simp}; simp [h]
  exact (go #[] _ _ rfl).symm

/--
Left-biased version of `List.zipWith`. `zipWithLeft' f as bs` applies `f` to each
pair of elements `aᵢ ∈ as` and `bᵢ ∈ bs`. If `bs` is shorter than `as`, `f` is
applied to `none` for the remaining `aᵢ`. Returns the results of the `f`
applications and the remaining `bs`.
```
zipWithLeft' prod.mk [1, 2] ['a'] = ([(1, some 'a'), (2, none)], [])
zipWithLeft' prod.mk [1] ['a', 'b'] = ([(1, some 'a')], ['b'])
```
-/
@[simp] def zipWithLeft' (f : α → Option β → γ) : List α → List β → List γ × List β
  | [], bs => ([], bs)
  | a :: as, [] => ((a :: as).map fun a => f a none, [])
  | a :: as, b :: bs => let r := zipWithLeft' f as bs; (f a (some b) :: r.1, r.2)

/-- Tail-recursive version of `zipWithLeft'`. -/
@[inline] def zipWithLeft'TR (f : α → Option β → γ)
    (as : List α) (bs : List β) : List γ × List β := go as bs #[] where
  /-- Auxiliary for `zipWithLeft'TR`: `zipWithLeft'TR.go l acc = acc.toList ++ zipWithLeft' l`. -/
  go : List α → List β → Array γ → List γ × List β
  | [], bs, acc => (acc.toList, bs)
  | as, [], acc => (as.foldl (fun acc a => acc.push (f a none)) acc |>.toList, [])
  | a :: as, b :: bs, acc => go as bs (acc.push (f a (some b)))

@[csimp] theorem zipWithLeft'_eq_zipWithLeft'TR : @zipWithLeft' = @zipWithLeft'TR := by
  funext α β γ f as bs; simp [zipWithLeft'TR]
  let rec go (acc) : ∀ as bs, zipWithLeft'TR.go f as bs acc =
      let (l, r) := as.zipWithLeft' f bs; (acc.toList ++ l, r)
  | [], bs => by simp [zipWithLeft'TR.go]
  | _::_, [] => by simp [zipWithLeft'TR.go, Array.foldl_data_eq_map]
  | a::as, b::bs => by simp [zipWithLeft'TR.go, go _ as bs]
  simp [zipWithLeft'TR, go]

/--
Right-biased version of `List.zipWith`. `zipWithRight' f as bs` applies `f` to each
pair of elements `aᵢ ∈ as` and `bᵢ ∈ bs`. If `as` is shorter than `bs`, `f` is
applied to `none` for the remaining `bᵢ`. Returns the results of the `f`
applications and the remaining `as`.
```
zipWithRight' prod.mk [1] ['a', 'b'] = ([(some 1, 'a'), (none, 'b')], [])
zipWithRight' prod.mk [1, 2] ['a'] = ([(some 1, 'a')], [2])
```
-/
@[inline] def zipWithRight' (f : Option α → β → γ) (as : List α) (bs : List β) : List γ × List α :=
  zipWithLeft' (flip f) bs as

/--
Left-biased version of `List.zip`. `zipLeft' as bs` returns the list of
pairs `(aᵢ, bᵢ)` for `aᵢ ∈ as` and `bᵢ ∈ bs`. If `bs` is shorter than `as`, the
remaining `aᵢ` are paired with `none`. Also returns the remaining `bs`.
```
zipLeft' [1, 2] ['a'] = ([(1, some 'a'), (2, none)], [])
zipLeft' [1] ['a', 'b'] = ([(1, some 'a')], ['b'])
zipLeft' = zipWithLeft' prod.mk
```
-/
@[inline] def zipLeft' : List α → List β → List (α × Option β) × List β := zipWithLeft' Prod.mk

/--
Right-biased version of `List.zip`. `zipRight' as bs` returns the list of
pairs `(aᵢ, bᵢ)` for `aᵢ ∈ as` and `bᵢ ∈ bs`. If `as` is shorter than `bs`, the
remaining `bᵢ` are paired with `none`. Also returns the remaining `as`.
```
zipRight' [1] ['a', 'b'] = ([(some 1, 'a'), (none, 'b')], [])
zipRight' [1, 2] ['a'] = ([(some 1, 'a')], [2])
zipRight' = zipWithRight' prod.mk
```
-/
@[inline] def zipRight' : List α → List β → List (Option α × β) × List α := zipWithRight' Prod.mk

/--
Left-biased version of `List.zipWith`. `zipWithLeft f as bs` applies `f` to each pair
`aᵢ ∈ as` and `bᵢ ‌∈ bs`. If `bs` is shorter than `as`, `f` is applied to `none`
for the remaining `aᵢ`.
```
zipWithLeft prod.mk [1, 2] ['a'] = [(1, some 'a'), (2, none)]
zipWithLeft prod.mk [1] ['a', 'b'] = [(1, some 'a')]
zipWithLeft f as bs = (zipWithLeft' f as bs).fst
```
-/
@[simp] def zipWithLeft (f : α → Option β → γ) : List α → List β → List γ
  | [], _ => []
  | a :: as, [] => (a :: as).map fun a => f a none
  | a :: as, b :: bs => f a (some b) :: zipWithLeft f as bs

/-- Tail-recursive version of `zipWithLeft`. -/
@[inline] def zipWithLeftTR (f : α → Option β → γ)
    (as : List α) (bs : List β) : List γ := go as bs #[] where
  /-- Auxiliary for `zipWithLeftTR`: `zipWithLeftTR.go l acc = acc.toList ++ zipWithLeft l`. -/
  go : List α → List β → Array γ → List γ
  | [], _, acc => acc.toList
  | as, [], acc => as.foldl (fun acc a => acc.push (f a none)) acc |>.toList
  | a :: as, b :: bs, acc => go as bs (acc.push (f a (some b)))

@[csimp] theorem zipWithLeft_eq_zipWithLeftTR : @zipWithLeft = @zipWithLeftTR := by
  funext α β γ f as bs; simp [zipWithLeftTR]
  let rec go (acc) : ∀ as bs, zipWithLeftTR.go f as bs acc = acc.toList ++ as.zipWithLeft f bs
  | [], bs => by simp [zipWithLeftTR.go]
  | _::_, [] => by simp [zipWithLeftTR.go, Array.foldl_data_eq_map]
  | a::as, b::bs => by simp [zipWithLeftTR.go, go _ as bs]
  simp [zipWithLeftTR, go]

/--
Right-biased version of `List.zipWith`. `zipWithRight f as bs` applies `f` to each
pair `aᵢ ∈ as` and `bᵢ ‌∈ bs`. If `as` is shorter than `bs`, `f` is applied to
`none` for the remaining `bᵢ`.
```
zipWithRight prod.mk [1, 2] ['a'] = [(some 1, 'a')]
zipWithRight prod.mk [1] ['a', 'b'] = [(some 1, 'a'), (none, 'b')]
zipWithRight f as bs = (zipWithRight' f as bs).fst
```
-/
@[inline] def zipWithRight (f : Option α → β → γ) (as : List α) (bs : List β) : List γ :=
  zipWithLeft (flip f) bs as

/--
Left-biased version of `List.zip`. `zipLeft as bs` returns the list of pairs
`(aᵢ, bᵢ)` for `aᵢ ∈ as` and `bᵢ ∈ bs`. If `bs` is shorter than `as`, the
remaining `aᵢ` are paired with `none`.
```
zipLeft [1, 2] ['a'] = [(1, some 'a'), (2, none)]
zipLeft [1] ['a', 'b'] = [(1, some 'a')]
zipLeft = zipWithLeft prod.mk
```
-/
@[inline] def zipLeft : List α → List β → List (α × Option β) := zipWithLeft Prod.mk

/--
Right-biased version of `List.zip`. `zipRight as bs` returns the list of pairs
`(aᵢ, bᵢ)` for `aᵢ ∈ as` and `bᵢ ∈ bs`. If `as` is shorter than `bs`, the
remaining `bᵢ` are paired with `none`.
```
zipRight [1, 2] ['a'] = [(some 1, 'a')]
zipRight [1] ['a', 'b'] = [(some 1, 'a'), (none, 'b')]
zipRight = zipWithRight prod.mk
```
-/
@[inline] def zipRight : List α → List β → List (Option α × β) := zipWithRight Prod.mk

/--
If all elements of `xs` are `some xᵢ`, `allSome xs` returns the `xᵢ`. Otherwise
it returns `none`.
```
allSome [some 1, some 2] = some [1, 2]
allSome [some 1, none  ] = none
```
-/
@[inline] def allSome (l : List (Option α)) : Option (List α) := l.mapM id

/--
`fillNones xs ys` replaces the `none`s in `xs` with elements of `ys`. If there
are not enough `ys` to replace all the `none`s, the remaining `none`s are
dropped from `xs`.
```
fillNones [none, some 1, none, none] [2, 3] = [2, 1, 3]
```
-/
@[simp] def fillNones {α} : List (Option α) → List α → List α
  | [], _ => []
  | some a :: as, as' => a :: fillNones as as'
  | none :: as, [] => as.reduceOption
  | none :: as, a :: as' => a :: fillNones as as'

/-- Tail-recursive version of `fillNones`. -/
@[inline] def fillNonesTR (as : List (Option α)) (as' : List α) : List α := go as as' #[] where
  /-- Auxiliary for `fillNonesTR`: `fillNonesTR.go as as' acc = acc.toList ++ fillNones as as'`. -/
  go : List (Option α) → List α → Array α → List α
  | [], _, acc => acc.toList
  | some a :: as, as', acc => go as as' (acc.push a)
  | none :: as, [], acc => filterMapTR.go id as acc
  | none :: as, a :: as', acc => go as as' (acc.push a)

@[csimp] theorem fillNones_eq_fillNonesTR : @fillNones = @fillNonesTR := by
  funext α as as'; simp [fillNonesTR]
  let rec go (acc) : ∀ as as', @fillNonesTR.go α as as' acc = acc.data ++ as.fillNones as'
  | [], _ => by simp [fillNonesTR.go]
  | some a :: as, as' => by simp [fillNonesTR.go, go _ as as']
  | none :: as, [] => by simp [fillNonesTR.go, reduceOption, filterMap_eq_filterMapTR.go]
  | none :: as, a :: as' => by simp [fillNonesTR.go, go _ as as']
  simp [fillNonesTR, go]

/--
`takeList as ns` extracts successive sublists from `as`. For `ns = n₁ ... nₘ`,
it first takes the `n₁` initial elements from `as`, then the next `n₂` ones,
etc. It returns the sublists of `as` -- one for each `nᵢ` -- and the remaining
elements of `as`. If `as` does not have at least as many elements as the sum of
the `nᵢ`, the corresponding sublists will have less than `nᵢ` elements.
```
takeList ['a', 'b', 'c', 'd', 'e'] [2, 1, 1] = ([['a', 'b'], ['c'], ['d']], ['e'])
takeList ['a', 'b'] [3, 1] = ([['a', 'b'], []], [])
```
-/
def takeList {α} : List α → List Nat → List (List α) × List α
  | xs, [] => ([], xs)
  | xs, n :: ns =>
    let (xs₁, xs₂) := xs.splitAt n
    let (xss, rest) := takeList xs₂ ns
    (xs₁ :: xss, rest)

/-- Tail-recursive version of `takeList`. -/
@[inline] def takeListTR
    (xs : List α) (ns : List Nat) : List (List α) × List α := go ns xs #[] where
  /-- Auxiliary for `takeListTR`: `takeListTR.go as as' acc = acc.toList ++ takeList as as'`. -/
  go : List Nat → List α → Array (List α) → List (List α) × List α
  | [], xs, acc => (acc.toList, xs)
  | n :: ns, xs, acc =>
    let (xs₁, xs₂) := xs.splitAt n
    go ns xs₂ (acc.push xs₁)

@[csimp] theorem takeList_eq_takeListTR : @takeList = @takeListTR := by
  funext α xs ns; simp [takeListTR]
  let rec go (acc) : ∀ ns xs, @takeListTR.go α ns xs acc =
      let (l, r) := xs.takeList ns; (acc.toList ++ l, r)
  | [], xs => by simp [takeListTR.go, takeList]
  | n::ns, xs => by simp [takeListTR.go, takeList, go _ ns]
  simp [takeListTR, go]

/-- Auxliary definition used to define `toChunks`.
  `toChunksAux n xs i` returns `(xs.take i, (xs.drop i).toChunks (n+1))`,
  that is, the first `i` elements of `xs`, and the remaining elements chunked into
  sublists of length `n+1`. -/
def toChunksAux {α} (n : Nat) : List α → Nat → List α × List (List α)
  | [], _ => ([], [])
  | x :: xs, 0 =>
    let (l, L) := toChunksAux n xs n
    ([], (x :: l) :: L)
  | x :: xs, i+1 =>
    let (l, L) := toChunksAux n xs i
    (x :: l, L)

/--
`xs.toChunks n` splits the list into sublists of size at most `n`,
such that `(xs.toChunks n).join = xs`.
```
[1, 2, 3, 4, 5, 6, 7, 8].toChunks 10 = [[1, 2, 3, 4, 5, 6, 7, 8]]
[1, 2, 3, 4, 5, 6, 7, 8].toChunks 3 = [[1, 2, 3], [4, 5, 6], [7, 8]]
[1, 2, 3, 4, 5, 6, 7, 8].toChunks 2 = [[1, 2], [3, 4], [5, 6], [7, 8]]
[1, 2, 3, 4, 5, 6, 7, 8].toChunks 0 = [[1, 2, 3, 4, 5, 6, 7, 8]]
```
-/
def toChunks {α} : Nat → List α → List (List α)
  | _, [] => []
  | 0, xs => [xs]
  | n, x :: xs =>
    let rec
    /-- Auxliary definition used to define `toChunks`.
    `toChunks.go xs acc₁ acc₂` pushes elements into `acc₁` until it reaches size `n`,
    then it pushes the resulting list to `acc₂` and continues until `xs` is exhausted. -/
    go : List α → Array α → Array (List α) → List (List α)
    | [], acc₁, acc₂ => acc₂.push acc₁.toList |>.toList
    | x :: xs, acc₁, acc₂ =>
      if acc₁.size == n then
        go xs ((Array.mkEmpty n).push x) (acc₂.push acc₁.toList)
      else
        go xs (acc₁.push x) acc₂
    go xs #[x] #[]

/-!
We add some n-ary versions of `List.zipWith` for functions with more than two arguments.
These can also be written in terms of `List.zip` or `List.zipWith`.
For example, `zipWith₃ f xs ys zs` could also be written as
`zipWith id (zipWith f xs ys) zs`
or as
`(zip xs <| zip ys zs).map fun ⟨x, y, z⟩ => f x y z`.
-/

-- TODO(Mario): tail recursive
/-- Ternary version of `List.zipWith`. -/
def zipWith₃ (f : α → β → γ → δ) : List α → List β → List γ → List δ
  | x :: xs, y :: ys, z :: zs => f x y z :: zipWith₃ f xs ys zs
  | _, _, _ => []

/-- Quaternary version of `List.zipWith`. -/
def zipWith₄ (f : α → β → γ → δ → ε) : List α → List β → List γ → List δ → List ε
  | x :: xs, y :: ys, z :: zs, u :: us => f x y z u :: zipWith₄ f xs ys zs us
  | _, _, _, _ => []

/-- Quinary version of `List.zipWith`. -/
def zipWith₅ (f : α → β → γ → δ → ε → ζ) : List α → List β → List γ → List δ → List ε → List ζ
  | x :: xs, y :: ys, z :: zs, u :: us, v :: vs => f x y z u v :: zipWith₅ f xs ys zs us vs
  | _, _, _, _, _ => []

/-- An auxiliary function for `List.mapWithPrefixSuffix`. -/
-- TODO(Mario): tail recursive
def mapWithPrefixSuffixAux {α β} (f : List α → α → List α → β) : List α → List α → List β
  | _, [] => []
  | prev, h :: t => f prev h t :: mapWithPrefixSuffixAux f (prev.concat h) t

/--
`List.mapWithPrefixSuffix f l` maps `f` across a list `l`.
For each `a ∈ l` with `l = pref ++ [a] ++ suff`, `a` is mapped to `f pref a suff`.
Example: if `f : list Nat → Nat → list Nat → β`,
`List.mapWithPrefixSuffix f [1, 2, 3]` will produce the list
`[f [] 1 [2, 3], f [1] 2 [3], f [1, 2] 3 []]`.
-/
def mapWithPrefixSuffix {α β} (f : List α → α → List α → β) (l : List α) : List β :=
  mapWithPrefixSuffixAux f [] l

/--
`List.mapWithComplement f l` is a variant of `List.mapWithPrefixSuffix`
that maps `f` across a list `l`.
For each `a ∈ l` with `l = pref ++ [a] ++ suff`, `a` is mapped to `f a (pref ++ suff)`,
i.e., the list input to `f` is `l` with `a` removed.
Example: if `f : Nat → list Nat → β`, `List.mapWithComplement f [1, 2, 3]` will produce the list
`[f 1 [2, 3], f 2 [1, 3], f 3 [1, 2]]`.
-/
def mapWithComplement {α β} (f : α → List α → β) : List α → List β :=
  mapWithPrefixSuffix fun pref a suff => f a (pref ++ suff)

/--
Map each element of a `List` to an action, evaluate these actions in order,
and collect the results.
-/
protected def traverse [Applicative F] (f : α → F β) : List α → F (List β)
  | [] => pure []
  | x :: xs => List.cons <$> f x <*> List.traverse f xs

/--
`Perm l₁ l₂` or `l₁ ~ l₂` asserts that `l₁` and `l₂` are permutations
of each other. This is defined by induction using pairwise swaps.
-/
inductive Perm : List α → List α → Prop
  /-- `[] ~ []` -/
  | nil : Perm [] []
  /-- `l₁ ~ l₂ → x::l₁ ~ x::l₂` -/
  | cons (x : α) {l₁ l₂ : List α} : Perm l₁ l₂ → Perm (x :: l₁) (x :: l₂)
  /-- `x::y::l ~ y::x::l` -/
  | swap (x y : α) (l : List α) : Perm (y :: x :: l) (x :: y :: l)
  /-- `Perm` is transitive. -/
  | trans {l₁ l₂ l₃ : List α} : Perm l₁ l₂ → Perm l₂ l₃ → Perm l₁ l₃

@[inherit_doc] scoped infixl:50 " ~ " => Perm

/--
`O(|l₁| * |l₂|)`. Computes whether `l₁` is a permutation of `l₂`. See `isPerm_iff` for a
characterization in terms of `List.Perm`.
-/
def isPerm [BEq α] : List α → List α → Bool
  | [], l₂ => l₂.isEmpty
  | a :: l₁, l₂ => l₂.contains a && l₁.isPerm (l₂.erase a)

/--
`Subperm l₁ l₂`, denoted `l₁ <+~ l₂`, means that `l₁` is a sublist of
a permutation of `l₂`. This is an analogue of `l₁ ⊆ l₂` which respects
multiplicities of elements, and is used for the `≤` relation on multisets.
-/
def Subperm (l₁ l₂ : List α) : Prop := ∃ l, l ~ l₁ ∧ l <+ l₂

@[inherit_doc] scoped infixl:50 " <+~ " => Subperm

/--
`O(|l₁| * (|l₁| + |l₂|))`. Computes whether `l₁` is a sublist of a permutation of `l₂`.
See `isSubperm_iff` for a characterization in terms of `List.Subperm`.
-/
def isSubperm [BEq α] (l₁ l₂ : List α) : Bool := ∀ x ∈ l₁, count x l₁ ≤ count x l₂

/--
`O(|l| + |r|)`. Merge two lists using `s` as a switch.
-/
def merge (s : α → α → Bool) (l r : List α) : List α :=
  loop l r []
where
  /-- Inner loop for `List.merge`. Tail recursive. -/
  loop : List α → List α → List α → List α
  | [], r, t => reverseAux t r
  | l, [], t => reverseAux t l
  | a::l, b::r, t => bif s a b then loop l (b::r) (a::t) else loop (a::l) r (b::t)
