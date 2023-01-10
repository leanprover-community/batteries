/-
Copyright (c) 2022 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

namespace Ordering

/--
Check whether the ordering is 'equal'.
-/
def isEq : Ordering → Bool
  | eq => true
  | _ => false

/--
Check whether the ordering is 'not equal'.
-/
def isNe : Ordering → Bool
  | eq => false
  | _ => true

/--
Check whether the ordering is 'less than'.
-/
def isLT : Ordering → Bool
  | lt => true
  | _ => false

/--
Check whether the ordering is 'greater than'.
-/
def isGT : Ordering → Bool
  | gt => true
  | _ => false

/--
Check whether the ordering is 'greater than or equal'.
-/
def isGE : Ordering → Bool
  | lt => false
  | _ => true

end Ordering

/--
First compare `a` and `b` by cmp₁. If this returns 'equal', compare `c` and `d`
by `cmp₂`.
-/
def compareLex' (cmp₁ : α → β → Ordering) (a : α) (b : β)
    (cmp₂ : γ → δ → Ordering) (c : γ) (d : δ) : Ordering :=
  match cmp₁ a b with
  | .eq => cmp₂ c d
  | ord => ord

/--
Compare `a` and `b` lexicographically by `cmp₁` and `cmp₂`. `a` and `b` are
first compared by `cmp₁`. If this returns 'equal', `a` and `b` are compared
by `cmp₂` to break the tie.
-/
def compareLex (cmp₁ cmp₂ : α → β → Ordering) (a : α) (b : β) : Ordering :=
  compareLex' cmp₁ a b cmp₂ a b

/--
Compare `x` and `y` by comparing `f x` and `f y`.
-/
def compareOn [ord : Ord β] (f : α → β) (x y : α) : Ordering :=
  compare (f x) (f y)


namespace Ord

/--
Derive a `BEq` instance from an `Ord` instance.
-/
protected def toBEq (ord : Ord α) : BEq α where
  beq x y := ord.compare x y == .eq

/--
Derive an `LT` instance from an `Ord` instance.
-/
protected def toLT (_ : Ord α) : LT α :=
  ltOfOrd

/--
Derive an `LE` instance from an `Ord` instance.
-/
protected def toLE (_ : Ord α) : LE α :=
  leOfOrd

/--
Invert the order of an `Ord` instance.
-/
protected def opposite (ord : Ord α) : Ord α where
  compare x y := ord.compare y x

/--
`ord.on f` compares `x` and `y` by comparing `f x` and `f y` according to `ord`.
-/
protected def on (ord : Ord β) (f : α → β) : Ord α where
  compare := compareOn f

/--
Derive the lexicographic order on products `α × β` from orders for `α` and `β`.
-/
protected def lex (_ : Ord α) (_ : Ord β) : Ord (α × β) :=
  lexOrd

/--
Create an order which compares elements first by `ord₁` and then, if this
returns 'equal', by `ord₂`.
-/
protected def lex' (ord₁ ord₂ : Ord α) : Ord α where
  compare := compareLex ord₁.compare ord₂.compare
