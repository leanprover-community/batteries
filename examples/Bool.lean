import Std -- For examples and testing

-- # Boolean and Propositional Reasoning
def header := true

/-
This document describe's Lean's support for Boolean and propositional
reasoning.  It assumes the reader is familiar with Lean including basic
operations on `Bool` and `Prop` as well as common tactics such as `simp`
and `rfl`.

The documented is primarily intended as a reference for understanding
what operations are available for Boolean and propositional reasoning,
what the design goals are in the specification of theorems about them,
and the intended normal forms for the simplifier (with and without
simprocs).

This document is organized as follows: We first describe the definitions
that are in the scope of `Boolean and Propositional reasoning` for the
purposes of this document.  We then next describe the fundamental
algebraic laws that need to be covered by the theory and how they map
into lemmas.  Finally, we discuss our simplifier normalization strategy
and give advice for how to discharge proof obligations that are not
covered by the simplifier normalization strategy.
-/

-- # Scope of Boolean operators in Lean
def scope := true

/-
Lean is based on dependent type theory, and proof assistents based on
dependent type have not just a single type `Bool` for Boolean reasoning,
but also an infinite family of propositions (called `Prop` in Lean).
Each proposition `p` or its negation `¬p` is true in Lean using
classical reasoning.

One consequence of the distinction between `Bool` and instances of
`Prop` is that for each `Boolean` operation (in the traditional
mathematical sense), there is usually two or more operations in
Lean for operating with `Prop` and `Bool` respectively.

| Operator    | `Prop`              | `Bool`                          |
| ----------- | ------------------- | ------------------------------- |
| Complement  | `Not` (`¬p)`        | `not` (`!p`)                    |
| Conjunction | `And` (`p ∧ q`)     | `and` (`p && q`)                |
| Disjunction | `Or` (`p ∧ q`)      | `or`  (`p && q`)                |
| Equality    | `Eq`, `Iff`         | `BEq.beq` (`p == q`)            |
| Inequality  | `Ne` (`p ≠ q`)      | `bne` (`p != q`), `xor` (`Std`) |
| Implication | `p -> q`            | none                            |
| Choice      | (`d`)`ite` (`if..`) | `cond` (`bif...`)               |

There are coercisions that conflate the two.

* Every `b : Bool` can be automatically coerced into a `Prop` by
  introducing `b = true`.
* Every `p : Prop` with `[Decidable p]` instance can be coerced into
  a `Bool`.  There is a scoped non-executable low-priority instance
  in `Classical` so potentially every `Prop` can be coerced to a
  `Bool`.

`BEq` introduces a polymorphic equality comparison operator a well as
an inequality comparison `bne` defined as it's negation.  There is an
instance over `Bool` so `bne` is quivalent to exclusive or.

`LawfulBeq` uses two properties to capture equivalence between `==` and `=`.

-/


-- ## General Theorems in Lean
def theorems := true

/-
Boolean algebras have many well-known algebraic laws:

  * Not `!x` is a self inverse: `!!x = x`
  * `&&` and `||` are associative, commutative, and idempotent.
  * Demorgan's laws `!(a && b) = (!a || !b)`
  * And: `x && false = false`, `x && true  = x`, `x && !x = false`
  * Or:  `x || true  = true`, `x || false = x`, `x || !x = true`
  * `&&` and `||` distributes over each other:
    - `x && (y || z) = x && y || x && z`
    - `x || (y && z) = x || y && x || z`
  * `a -> b = !a || b`.  Also is reflexive and transitive
  * `xor a b = !(a == b)`
  * Equality `==` and `xor`/`bne` are associative, commutative
  * Equality is reflexive and xor irreflexive
  * Equality has identity true, xor has identity false
  * `cond c a b = c && a || !c && b`
    - Many simplification rules often apply.
-/
