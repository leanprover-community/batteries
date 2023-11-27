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
Discrimination tree key. See `DiscrTree`
-/
inductive Key where
  /-- `Key.const` takes a `Name` and an arity. -/
  | const  : Name → Nat → Key
  /-- `Key.fvar` takes an index and an arity. -/
  | fvar   : Nat → Nat → Key
  /-- `Key.bvar` takes an index and an arity. -/
  | bvar   : Nat → Nat → Key
  /-- `Key.star` takes an index. -/
  | star   : Nat → Key
  | lit    : Literal → Key
  | sort   : Key
  | lam    : Key
  | forall : Key
  /-- `Key.proj` takes the constructor `Name`, the projection index and the arity. -/
  | proj   : Name → Nat → Nat → Key
  deriving Inhabited, BEq, Repr

protected def Key.hash : Key → UInt64
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

def Key.lt : Key → Key → Bool
  | .star i₁,       .star i₂       => i₁ < i₂
  | .lit v₁,        .lit v₂        => v₁ < v₂
  | .fvar n₁ a₁,    .fvar n₂ a₂    => n₁ < n₂ || (n₁ == n₂ && a₁ < a₂)
  | .const n₁ a₁,   .const n₂ a₂   => Name.quickLt n₁ n₂ || (n₁ == n₂ && a₁ < a₂)
  | .proj s₁ i₁ a₁, .proj s₂ i₂ a₂ => Name.quickLt s₁ s₂ || (s₁ == s₂ && i₁ < i₂) || (s₁ == s₂ && i₁ == i₂ && a₁ < a₂)
  | .bvar i₁ a₁,    .bvar i₂ a₂    => i₁ < i₂ || (i₁ == i₂ && a₁ < a₂)
  | k₁,             k₂             => k₁.ctorIdx < k₂.ctorIdx

instance : LT Key := ⟨fun a b => Key.lt a b⟩
instance (a b : Key) : Decidable (a < b) := inferInstanceAs (Decidable (Key.lt a b))

def Key.format : Key → Format
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
  | node (children : Array (Key × Trie α))
  | path (keys : Array Key) (child : Trie α)
  | values (vs : Array α)
instance : Inhabited (Trie α) := ⟨.node #[]⟩

/-- Smart `Trie.path` constructor that only adds the path if it is non-empty.
we always use this constructor, so that paths are always non-empty. -/
def Trie.mkPath (keys : Array Key) (child : Trie α) :=
  if keys.isEmpty then child else Trie.path keys child

def Trie.singleton (keys : Array Key) (value : α) (i : Nat) : Trie α :=
  mkPath keys[i:] (values #[value])

def Trie.mkNode2 (k1 : Key) (t1 : Trie α) (k2 : Key) (t2 : Trie α) : Trie α :=
  if k1 < k2 then
    .node #[(k1, t1), (k2, t2)]
  else
    .node #[(k2, t2), (k1, t1)]

def Trie.values! : Trie α → Array α
  | .values vs => vs
  | _ => panic! "resulting Trie is not .values"

def Trie.children! : Trie α → Array (Key × Trie α)
| .node cs => cs
| .path ks c => #[(ks[0]!, mkPath ks[1:] c)]
| .values _ => panic! "did not expect .values constructor"

partial def Trie.format [ToFormat α] : Trie α → Format
  | .node cs => Format.group $ Format.paren $
    "node" ++ Format.join (cs.toList.map fun (k, c) => Format.line ++ Format.paren (Std.format k ++ " => " ++ format c))
  | .values vs => "values" ++ if vs.isEmpty then Format.nil else " " ++ Std.format vs
  | .path ks c => Std.format ks ++ " => " ++ format c

instance [ToFormat α] : ToFormat (Trie α) := ⟨Trie.format⟩



/-- `DTExpr` is a simplified form of `Expr`, used as an intermediate step for translating from `Expr` to `Array Key`. -/
inductive DTExpr where
  | const  : Name → Array DTExpr → DTExpr
  | fvar   : FVarId → Array DTExpr → DTExpr
  | bvar   : Nat → Array DTExpr → DTExpr
  | star   : MVarId → DTExpr
  | lit    : Literal → DTExpr
  | sort   : DTExpr
  | lam    : DTExpr → DTExpr
  | forall : DTExpr → DTExpr → DTExpr
  | proj   : Name → Nat → DTExpr → Array DTExpr → DTExpr
deriving Inhabited


partial def DTExpr.format : DTExpr → Format
  | .star _                 => "*"
  | .sort                   => "◾"
  | .lit (Literal.natVal v) => Std.format v
  | .lit (Literal.strVal v) => repr v
  | .const n as             => Std.format n  ++ if as.isEmpty then .nil else Format.paren (@Format.joinSep _ ⟨DTExpr.format⟩ as.toList ", ")
  | .proj _ i a as          => DTExpr.format a ++ "." ++ Std.format i ++ if as.isEmpty then .nil else " " ++ Format.paren (@Format.joinSep _ ⟨DTExpr.format⟩ as.toList ", ")
  | .fvar n as              => "f" ++ n.1.toString ++ if as.isEmpty then .nil else Format.paren (@Format.joinSep _ ⟨DTExpr.format⟩ as.toList ", ")
  | .bvar i as              => "#" ++ Std.format i  ++ if as.isEmpty then .nil else Format.paren (@Format.joinSep _ ⟨DTExpr.format⟩ as.toList ", ")
  | .forall d b             => DTExpr.format d ++ " → " ++ DTExpr.format b
  | .lam b                  => "λ " ++ DTExpr.format b

instance : ToFormat DTExpr := ⟨DTExpr.format⟩

end DiscrTree

open DiscrTree
/--
Discrimination trees. It is an index from terms to values of type `α`.
-/
structure DiscrTree (α : Type) where
  root : PersistentHashMap Key (Trie α) := {}
deriving Inhabited

partial def DiscrTree.format [ToFormat α] (d : DiscrTree α) : Format :=
  let (_, r) := d.root.foldl
    (fun (p : Bool × Format) k c =>
      (false, p.2 ++ (if p.1 then Format.nil else Format.line) ++ Format.paren (Std.format k ++ " => " ++ Std.format c)))
    (true, Format.nil)
  Format.group r

instance [ToFormat α] : ToFormat (DiscrTree α) := ⟨DiscrTree.format⟩
