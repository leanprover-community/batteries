/-
Copyright (c) 2023 J. W. Gerbscheid. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: J. W. Gerbscheid
-/
import Lean.Expr

/-! See file `DiscrTree.lean` for the actual implementation and documentation. -/

open Lean

namespace Std.DiscrTree

/--
Discrimination tree key.  See `DiscrTree`.
-/
inductive Key where
  /-- `.const` takes a `Name` and an arity. -/
  | const  : Name → Nat → Key
  /-- `.fvar` takes an index and an arity. -/
  | fvar   : Nat → Nat → Key
  /-- A bound variable, from either a `.lam` or a `.forall`.
  `.bvar` takes an index and an arity. -/
  | bvar   : Nat → Nat → Key
  /-- A metavariable.
  `.star` takes an index. -/
  | star   : Nat → Key
  /-- A literal. -/
  | lit    : Literal → Key
  /-- A sort. Universe levels are ignored. -/
  | sort   : Key
  /-- A lambda function. -/
  | lam    : Key
  /-- A dependent arrow. -/
  | forall : Key
  /-- `.proj` takes the constructor `Name`, the projection index and the arity. -/
  | proj   : Name → Nat → Nat → Key
  deriving Inhabited, BEq, Repr

private nonrec def Key.hash : Key → UInt64
  | .const n a   => mixHash 5237 $ mixHash (hash n) (hash a)
  | .fvar n a    => mixHash 3541 $ mixHash (hash n) (hash a)
  | .bvar i a    => mixHash 4323 $ mixHash (hash i) (hash a)
  | .star i      => mixHash 7883 $ hash i
  | .lit v       => mixHash 1879 $ hash v
  | .sort        => 2411
  | .lam         => 4742
  | .«forall»    => 9752
  | .proj s i a  => mixHash (hash a) $ mixHash (hash s) (hash i)

instance : Hashable Key := ⟨Key.hash⟩

/-- `Key`'s are sorted in the first place by the constructor index.
Note that it is important that the index of the star pattern is 0,
because when looking up in a `Trie`, we look at the start of the sorted array
for all `.star` patterns. -/
def Key.ctorIdx : Key → Nat
  | .star ..  => 0
  | .sort     => 1
  | .lit ..   => 2
  | .fvar ..  => 3
  | .bvar ..  => 4
  | .lam      => 5
  | .forall   => 6
  | .proj ..  => 7
  | .const .. => 8

/-- The (arbitrary) order on `Key` used in the `DiscrTree`. -/
private def Key.lt : Key → Key → Bool
  | .star i₁,       .star i₂       => i₁ < i₂
  | .lit v₁,        .lit v₂        => v₁ < v₂
  | .fvar n₁ a₁,    .fvar n₂ a₂    => n₁ < n₂ || (n₁ == n₂ && a₁ < a₂)
  | .const n₁ a₁,   .const n₂ a₂   => Name.quickLt n₁ n₂ || (n₁ == n₂ && a₁ < a₂)
  | .proj s₁ i₁ a₁, .proj s₂ i₂ a₂ => Name.quickLt s₁ s₂ || (s₁ == s₂ && i₁ < i₂) || (s₁ == s₂ && i₁ == i₂ && a₁ < a₂)
  | .bvar i₁ a₁,    .bvar i₂ a₂    => i₁ < i₂ || (i₁ == i₂ && a₁ < a₂)
  | k₁,             k₂             => k₁.ctorIdx < k₂.ctorIdx

instance : LT Key := ⟨fun a b => Key.lt a b⟩
instance (a b : Key) : Decidable (a < b) := inferInstanceAs (Decidable (Key.lt a b))

private def Key.format : Key → Format
  | .star i                 => "*" ++ Std.format i
  | .sort                   => "◾"
  | .lit (Literal.natVal v) => Std.format v
  | .lit (Literal.strVal v) => repr v
  | .const k a              => "⟨" ++ Std.format k ++ ", " ++ Std.format a ++ "⟩"
  | .proj s i a             => "⟨" ++ Std.format s ++ "." ++ Std.format i ++ ", " ++ Std.format a ++ "⟩"
  | .fvar k a               => "⟨" ++ "f" ++ Std.format k ++ ", " ++ Std.format a ++ "⟩"
  | .bvar i a               => "⟨" ++ "#" ++ Std.format i ++ ", " ++ Std.format a ++ "⟩"
  | .forall                 => "→"
  | .lam                    => "λ"

instance : ToFormat Key := ⟨Key.format⟩

/-- Return the number of argumets that the `Key` takes. -/
def Key.arity : Key → Nat
  | .const _ a  => a
  | .fvar _ a   => a
  | .bvar _ a   => a
  | .lam        => 1
  | .forall     => 2
  | .proj _ _ a => 1 + a
  | _           => 0



/--
Discrimination tree trie. See `DiscrTree`.
-/
inductive Trie (α : Type) where
  /-- Map from `Key` to `Trie`. Children is an `Array` of size at least 2,
  sorted in increasing order using `Key.lt`. -/
  | node (children : Array (Key × Trie α))
  /-- Sequence of nodes with only one child. `keys` is an `Array` of size at least 1. -/
  | path (keys : Array Key) (child : Trie α)
  /-- Leaf of the Trie. values is an `Array` of size at least 1. -/
  | values (vs : Array α)
instance : Inhabited (Trie α) := ⟨.node #[]⟩

/-- `Trie.path` constructor that only inserts the path if it is non-empty. -/
def Trie.mkPath (keys : Array Key) (child : Trie α) :=
  if keys.isEmpty then child else Trie.path keys child

/-- `Trie` constructor for a single value. -/
def Trie.singleton (keys : Array Key) (value : α) (i : Nat) : Trie α :=
  mkPath keys[i:] (values #[value])

/-- `Trie.node` constructor for combining two `Key`, `Trie α` pairs. -/
def Trie.mkNode2 (k1 : Key) (t1 : Trie α) (k2 : Key) (t2 : Trie α) : Trie α :=
  if k1 < k2 then
    .node #[(k1, t1), (k2, t2)]
  else
    .node #[(k2, t2), (k1, t1)]

/-- Return the values from a `Trie α`, assuming that it is a leaf -/
def Trie.values! : Trie α → Array α
  | .values vs => vs
  | _ => panic! "expected .values constructor"

/-- Return the children of a `Trie α`, assuming that it is not a leaf.
The result is sorted by the `Key`'s -/
def Trie.children! : Trie α → Array (Key × Trie α)
| .node cs => cs
| .path ks c => #[(ks[0]!, mkPath ks[1:] c)]
| .values _ => panic! "did not expect .values constructor"

private partial def Trie.format [ToFormat α] : Trie α → Format
  | .node cs => Format.group $ Format.paren $
    "node" ++ Format.join (cs.toList.map fun (k, c) =>
      Format.line ++ Format.paren (Std.format k ++ " => " ++ format c))
  | .values vs => "values" ++ if vs.isEmpty then Format.nil else " " ++ Std.format vs
  | .path ks c => "path" ++ Std.format ks ++ Format.line ++ format c

instance [ToFormat α] : ToFormat (Trie α) := ⟨Trie.format⟩



/--
`DTExpr` is a simplified form of `Expr`.
It is intermediate step for going from `Expr` to `Array Key`. See `DiscrTree`. -/
inductive DTExpr where
  /-- A constant. -/
  | const  : Name → Array DTExpr → DTExpr
  /-- A free variable. -/
  | fvar   : FVarId → Array DTExpr → DTExpr
  /-- A bound variable. -/
  | bvar   : Nat → Array DTExpr → DTExpr
  /-- A meta variable. -/
  | star   : MVarId → DTExpr
  /-- A literal. -/
  | lit    : Literal → DTExpr
  /-- A sort. -/
  | sort   : DTExpr
  /-- A lambda function. -/
  | lam    : DTExpr → DTExpr
  /-- A dependent arrow. -/
  | forall : DTExpr → DTExpr → DTExpr
  /-- A projection. -/
  | proj   : Name → Nat → DTExpr → Array DTExpr → DTExpr
deriving Inhabited


private partial def DTExpr.format : DTExpr → Format
  | .star _                 => "*"
  | .sort                   => "◾"
  | .lit (Literal.natVal v) => Std.format v
  | .lit (Literal.strVal v) => repr v
  | .const n as             => Std.format n  ++ formatArray as
  | .proj _ i a as          => DTExpr.format a ++ "." ++ Std.format i ++ formatArray as
  | .fvar _ as              => "fvar" ++ formatArray as
  | .bvar i as              => "#" ++ Std.format i  ++ formatArray as
  | .forall d b             => DTExpr.format d ++ " → " ++ DTExpr.format b
  | .lam b                  => "λ " ++ DTExpr.format b
where
  formatArray (as : Array DTExpr) :=
    if as.isEmpty then .nil else " " ++ Format.paren (@Format.joinSep _ ⟨DTExpr.format⟩ as.toList ", ")

instance : ToFormat DTExpr := ⟨DTExpr.format⟩

end DiscrTree

open DiscrTree
/--
Discrimination tree. It is an index from expressions to values of type `α`.
-/
abbrev DiscrTree (α : Type) := PersistentHashMap Key (Trie α)

private partial def DiscrTree.format [ToFormat α] (d : DiscrTree α) : Format :=
  let (_, r) := d.foldl
    (fun (p : Bool × Format) k c =>
      (false, p.2 ++ (if p.1 then Format.nil else Format.line) ++ Format.paren (Std.format k ++ " => " ++ Std.format c)))
    (true, Format.nil)
  Format.group r

instance [ToFormat α] : ToFormat (DiscrTree α) := ⟨DiscrTree.format⟩
