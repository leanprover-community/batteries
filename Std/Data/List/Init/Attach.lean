/-
Copyright (c) 2023 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Std.Data.List.Init.Lemmas

namespace List

/-- Partial map. If `f : Π a, p a → β` is a partial function defined on
  `a : α` satisfying `p`, then `pmap f l h` is essentially the same as `map f l`
  but is defined only when all members of `l` satisfy `p`, using the proof
  to apply `f`. -/
@[simp] def pmap {p : α → Prop} (f : ∀ a, p a → β) : ∀ l : List α, (∀ a ∈ l, p a) → List β
  | [], _ => []
  | a :: l, H => f a (forall_mem_cons.1 H).1 :: pmap f l (forall_mem_cons.1 H).2

/--
Unsafe implementation of `attach`, taking advantage of the fact that the representation of
`List {x // x ∈ l}` is the same as the input `List α`.
(Someday, the compiler might do this optimization automatically, but until then...)
-/
@[inline] private unsafe def attachImpl (l : List α) : List {x // x ∈ l} := unsafeCast l

/-- "Attach" the proof that the elements of `l` are in `l` to produce a new list
  with the same elements but in the type `{x // x ∈ l}`. -/
@[implemented_by attachImpl] def attach (l : List α) : List {x // x ∈ l} :=
  pmap Subtype.mk l fun _ => id

/-- Implementation of `pmap` using the zero-copy version of `attach`. -/
@[inline] private def pmapImpl {p : α → Prop} (f : ∀ a, p a → β) (l : List α) (h : ∀ a ∈ l, p a) :
    List β := l.attach.map fun ⟨x, h'⟩ => f x (h _ h')

@[csimp] private theorem pmap_eq_pmapImpl : @pmap = @pmapImpl := by
  funext α β p f L h'
  let rec go : ∀ L' (hL' : ∀ ⦃x⦄, x ∈ L' → x ∈ L),
      pmap f L' (fun _ h => h' _ <| hL' h) =
      map (fun ⟨x, hx⟩ => f x (h' _ hx)) (pmap Subtype.mk L' hL')
  | nil, hL' => rfl
  | cons _ L', hL' => congrArg _ <| go L' fun _ hx => hL' (.tail _ hx)
  exact go L fun _ hx => hx
