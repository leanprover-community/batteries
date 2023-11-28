/-
Copyright (c) 2023 J. W. Gerbscheid. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: J. W. Gerbscheid
-/
import Std.Data.StateList
import Std.Data.List.Basic
import Lean.Meta

/-!
This file defines discrimination trees.
It is based on `DiscrTree` that is already present in Lean.
I document here what is not in the original.

We define discrimination trees for the purpose of unifying local expressions with library results.

These are the features that are not in Lean's discrimination trees:

- The constructor `Key.fvar` and `Key.star` now take a `Nat` as an argument, as an identifier.
  For example, the library pattern `a+a` is encoded as `[⟨Hadd.hadd, 6⟩, *0, *0, *0, *1, *2, *2]`.
  `*0` corresponds to the type of `a`, `*1` to the `Hadd` instance, and `*2` to `a`.
  This means that it will only match an expression `x+y` if `x` is definitionally equal to `y`.

  `Key.fvar` is used in lemmas like
  `Nat.exists_prime_and_dvd {n : ℕ} (hn : n ≠ 1) : ∃ p, Prime p ∧ p ∣ n`,
  where the part `Prime p` gets the pattern `[⟨Nat.Prime, 1⟩, .fvar 0 0]`.
  the first argument of `Key.fvar` is the identifier, and the second argument is the arity.

  If a discrimination tree is built locally, there is a need for a `Key.fvar` that takes an `FVarId`
  as an idenitifier, which is what the DiscrTree defined in Lean does, but this is of no use for us.

- The constructors `Key.lam`, `Key.forall` and `Key.bvar` have been introduced in order to allow for
  patterns under binders. For example, this allows for more specific matching with
  the left hand side of `Finset.sum_range_id (n : ℕ) : ∑ i in range n, i = n * (n - 1) / 2`

- We keep track of a matching score of a unification.
  This score represent the number of keys that had to be the same for the unification to succeed.
  For example, matching `(1 + 2) + 3` with `add_comm` gives a score of 3,
  since the pattern of commutativity is [⟨Hadd.hadd, 6⟩, *0, *0, *0, *1, *2, *3],
  so matching `⟨Hadd.hadd, 6⟩` gives 1 point,
  and matching `*0` two times after its first appearence gives another 2 points.
  Similarly, matching it with `add_assoc` gives a score of 7.

  TODO?: the third type parameter of `Hadd.hadd` is an outparam,
  so its matching should not be counted in the score.

- Patterns that have the potential to be η-reduced are put into the `DiscrTree` under all
  possible reduced key sequences. This is for terms of the form `fun x => f (?m x₁ .. xₙ)`, where
  `?m` is a metavariable, and for some `i`, `xᵢ = x`.
  For example, the pattern `Continuous fun y => Real.exp (f y)])`
  is indexed by
  `[⟨Continuous, 5⟩, *0, ⟨Real, 0⟩, *1, *2, λ, ⟨Real.exp⟩, *3]` and by
  `[⟨Continuous, 5⟩, *0, ⟨Real, 0⟩, *1, *2, ⟨Real.exp⟩]`
  so that it also comes up if you search with `Continuous Real.exp`.
  Similarly, `Continuous fun x => f x + g x`
  is indexed by
  `[⟨Continuous, 1⟩, λ, ⟨Hadd.hadd, 6⟩, *0, *0, *0, *1, *2, *3]` and by
  `[⟨Continuous, 1⟩, ⟨Hadd.hadd, 5⟩, *0, *0, *0, *1, *2]`.
-/

open Lean Meta

namespace Std.DiscrTree

-- ## Definitions

/-- Discrimination tree key. -/
inductive Key where
  /-- A constant. It stores a `Name` and an arity. -/
  | const  : Name → Nat → Key
  /-- A free variable. It stores an index and an arity. -/
  | fvar   : Nat → Nat → Key
  /-- A bound variable, from either a `.lam` or a `.forall`. It stores an index and an arity. -/
  | bvar   : Nat → Nat → Key
  /-- A metavariable. It stores an index. -/
  | star   : Nat → Key
  /-- A literal. -/
  | lit    : Literal → Key
  /-- A sort. Universe levels are ignored. -/
  | sort   : Key
  /-- A lambda function. -/
  | lam    : Key
  /-- A dependent arrow. -/
  | forall : Key
  /-- A projection. It takes the constructor name, the projection index and the arity. -/
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

/-- Constructor index as a help for ordering `Key`.
Note that the index of the star pattern is 0, so that when looking up in a `Trie`,
we can look at the start of the sorted array for all `.star` patterns. -/
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
  | .bvar i₁ a₁,    .bvar i₂ a₂    => i₁ < i₂ || (i₁ == i₂ && a₁ < a₂)
  | .proj s₁ i₁ a₁, .proj s₂ i₂ a₂ =>
    Name.quickLt s₁ s₂ || (s₁ == s₂ && (i₁ < i₂ || (i₁ == i₂ && a₁ < a₂)))
  | .const n₁ a₁,   .const n₂ a₂   => Name.quickLt n₁ n₂ || (n₁ == n₂ && a₁ < a₂)
  | k₁,             k₂             => k₁.ctorIdx < k₂.ctorIdx

instance : LT Key := ⟨fun a b => Key.lt a b⟩
instance (a b : Key) : Decidable (a < b) := inferInstanceAs (Decidable (Key.lt a b))

private def Key.format : Key → Format
  | .star i                 => "*" ++ Std.format i
  | .sort                   => "◾"
  | .lit (Literal.natVal v) => Std.format v
  | .lit (Literal.strVal v) => repr v
  | .const k a              => "⟨" ++ Std.format k ++ ", " ++ Std.format a ++ "⟩"
  | .proj s i a             => "⟨" ++ Std.format s ++"."++ Std.format i ++", "++ Std.format a ++ "⟩"
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


/-- Discrimination tree trie. See `DiscrTree`. -/
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



/-- `DTExpr` is a simplified form of `Expr`.
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
    if as.isEmpty
      then .nil
      else " " ++ Format.paren (@Format.joinSep _ ⟨DTExpr.format⟩ as.toList ", ")

instance : ToFormat DTExpr := ⟨DTExpr.format⟩


/-- Discrimination tree. It is an index from expressions to values of type `α`. -/
def _root_.Std.DiscrTree (α : Type) := PersistentHashMap Key (Trie α)

private partial def DiscrTree.format [ToFormat α] (d : DiscrTree α) : Format :=
  let (_, r) := d.foldl
    (fun (p : Bool × Format) k c =>
      (false,
        p.2 ++ (if p.1 then Format.nil else Format.line) ++
          Format.paren (Std.format k ++ " => " ++ Std.format c)))
    (true, Format.nil)
  Format.group r

instance [ToFormat α] : ToFormat (DiscrTree α) := ⟨DiscrTree.format⟩




-- ## Encoding an Expr

/-- This `MVarId` is used to represent expressions that should be indexed with a unique
`Key.star`. -/
private def tmpMVarId : MVarId := { name := `_discr_tree_tmp }
private def tmpStar : Expr := mkMVar tmpMVarId


/-- This state is used to turn the indexing by `MVarId` and `FVarId` in `DTExpr` into
indexing by `Nat` in `Key`. -/
private structure Flatten.State where
  stars : Array MVarId := #[]
  fvars : Array FVarId := #[]

private def getFVar (fvarId : FVarId) : StateM Flatten.State Nat :=
  modifyGet fun s =>
  match s.fvars.findIdx? (· == fvarId) with
  | some idx => (idx, s)
  | none => (s.fvars.size, { s with fvars := s.fvars.push fvarId })

private def getStar (mvarId : MVarId) : StateM Flatten.State Nat :=
  modifyGet fun s => Id.run do
    if mvarId != tmpMVarId then
      if let some idx := s.stars.findIdx? (· == mvarId) then
        return (idx, s)
    return (s.stars.size, { s with stars := s.stars.push mvarId })

private partial def DTExpr.flattenAux (todo : Array Key) : DTExpr → StateM Flatten.State (Array Key)
  | .const n args =>   args.foldlM (init := todo.push (.const n args.size)) flattenAux
  | .fvar i args => do args.foldlM (init := todo.push (.fvar (← getFVar i) args.size)) flattenAux
  | .bvar i args =>    args.foldlM (init := todo.push (.bvar i args.size)) flattenAux
  | .star i => return todo.push (.star (← getStar i))
  | .lit l => return todo.push (.lit l)
  | .sort => return todo.push .sort
  | .lam b => flattenAux (todo.push .lam) b
  | .«forall» d b => do flattenAux (← flattenAux (todo.push .forall) d) b
  | .proj n i e args => do
    args.foldlM (init := ← flattenAux (todo.push (.proj n i args.size)) e) flattenAux

/-- Given a `DTExpr`, return the linearized encoding in terms of `Key`,
which is used for `DiscrTree` indexing. -/
def DTExpr.flatten (e : DTExpr) (initCapacity := 16) : Array Key :=
  (DTExpr.flattenAux (.mkEmpty initCapacity) e).run' {}




/-- Return true if `a` should be ignored in the `DiscrTree`. -/
private def ignoreArg (a : Expr) (i : Nat) (infos : Array ParamInfo) : MetaM Bool := do
  if h : i < infos.size then
    let info := infos.get ⟨i, h⟩
    if info.isInstImplicit then
      return true
    else if info.isImplicit || info.isStrictImplicit then
      return !(← isType a)
    else
      isProof a
  else
    isProof a

/-- Replace the arguments that have to be ignored by the metavariable `tmpStar`. -/
private def ignoreArgs (infos : Array ParamInfo) (args : Array Expr) : MetaM (Array Expr) :=
  args.mapIdxM (fun i arg => return if ← ignoreArg arg i infos then tmpStar else arg)

/--
Return true if `e` is one of the following
- A nat literal (numeral)
- `Nat.zero`
- `Nat.succ x` where `isNumeral x`
- `OfNat.ofNat _ x _` where `isNumeral x` -/
private partial def isNumeral (e : Expr) : Bool :=
  if e.isNatLit then true
  else
    let f := e.getAppFn
    if !f.isConst then false
    else
      let fName := f.constName!
      if fName == ``Nat.succ && e.getAppNumArgs == 1 then isNumeral e.appArg!
      else if fName == ``OfNat.ofNat && e.getAppNumArgs == 3 then isNumeral (e.getArg! 1)
      else if fName == ``Nat.zero && e.getAppNumArgs == 0 then true
      else false

private partial def toNatLit? (e : Expr) : Option Literal :=
  if isNumeral e then
    if let some n := loop e then
      some (.natVal n)
    else
      none
  else
    none
where
  loop (e : Expr) : OptionT Id Nat := do
    let f := e.getAppFn
    match f with
    | .lit (.natVal n) => return n
    | .const fName .. =>
      if fName == ``Nat.succ && e.getAppNumArgs == 1 then
        let r ← loop e.appArg!
        return r+1
      else if fName == ``OfNat.ofNat && e.getAppNumArgs == 3 then
        loop (e.getArg! 1 3)
      else if fName == ``Nat.zero && e.getAppNumArgs == 0 then
        return 0
      else
        failure
    | _ => failure

/-- The weak head normal form function for indexing expressions in a `DiscrTree`. -/
partial def reduce (e : Expr) (config : WhnfCoreConfig) : MetaM Expr := do
  let e ← whnfCore e config
  match (← unfoldDefinition? e) with
  | some e => reduce e config
  | none => match e.etaExpandedStrict? with
    | some e => reduce e config
    | none   => return e



/-- Check whether the expression is represented by `Key.star`. -/
def isStar : Expr → Bool
  | .mvar .. => true
  | .app f _ => isStar f
  | _ => false

/-- Check whether the expression is represented by `Key.star` and has `arg` as an argument. -/
def isStarWithArg (arg : Expr) : Expr → Bool
  | .app f a => if a == arg then isStar f else isStarWithArg arg f
  | _ => false

private def starEtaExpandedBody : Expr → Nat → Nat → Option Expr
  | .app b a, n+1, i => if isStarWithArg (.bvar i) a then starEtaExpandedBody b n (i+1) else none
  | _,        _+1, _ => none
  | b,        0,   _ => some b

/-- If `e` is of the form `(fun x₀ ... xₙ => b y₀ ... yₙ)`,
where each `yᵢ` has a meta variable head with `xᵢ` as an argument,
then return `some b`. Otherwise, return `none`.
-/
def starEtaExpanded : Expr → Nat → Option Expr
  | .lam _ _ b _, n => starEtaExpanded b (n+1)
  | b,            n => starEtaExpandedBody b n 0


private partial def DTExpr.hasLooseBVarsAux (i : Nat) : DTExpr → Bool
  | .const _ as    => as.any (hasLooseBVarsAux i)
  | .fvar _ as     => as.any (hasLooseBVarsAux i)
  | .bvar j as     => j ≥ i || as.any (hasLooseBVarsAux i)
  | .proj _ _ a as => a.hasLooseBVarsAux i || as.any (hasLooseBVarsAux i)
  | .forall d b    => d.hasLooseBVarsAux i || b.hasLooseBVarsAux (i+1)
  | .lam b         => b.hasLooseBVarsAux (i+1)
  | _              => false

/-- Return `true` if `e` contains a loose bound variable. -/
def DTExpr.hasLooseBVars (e : DTExpr) : Bool :=
  e.hasLooseBVarsAux 0


namespace MkDTExpr

private structure Context where
  /-- Free variables that came from a lambda or forall binder.
  The list index gives the De Bruijn index. -/
  bvars : List FVarId := []
  /-- Free variables that come from a lambda that has been removed via η-reduction. -/
  unbvars : List FVarId := []

private abbrev M := ReaderT Context $ StateListT (AssocList Expr DTExpr) MetaM

/-
Caching values is a bit dangerous, because when two expressions are be equal and they live under
a different number of binders, then the resulting De Bruijn indices are offset.
In practice, getting a `.bvar` in a `DTExpr` is very rare, so we exclude such values from the cache.
-/
instance : MonadCache Expr DTExpr M where
  findCached? e := do
    let c ← get
    return c.find? e
  cache e e' :=
    if e'.hasLooseBVars then
      return
    else
      modify (·.insert e e')

/-- If `e` is of the form `(fun x₁ ... xₙ => b y₁ ... yₙ)`,
then introduce free variables for `x₁`, ..., `xₙ`, instantiate these in `b`, and run `k` on `b`. -/
partial def introEtaBVars [Inhabited α] (e b : Expr) (k : Expr → M α) : M α :=
  match e with
  | .lam n d e' _ =>
    withLocalDeclD n d fun fvar =>
      withReader (fun c => { c with unbvars := fvar.fvarId! :: c.unbvars }) $
        introEtaBVars e' (b.instantiate1 fvar) k
  | _ => k b

/-- Return all encodings of `e` as a `DTExpr`.
If `root = false`, then `e` is a strict sub expression of the original expression. -/
partial def mkDTExprAux (root : Bool) (config : WhnfCoreConfig) (e : Expr) : M DTExpr := do
  let e ← reduce e config
  Expr.withApp e fun fn args => do

  let argDTExprs : M (Array DTExpr) := do
    let info ← getFunInfoNArgs fn args.size
    let args ← ignoreArgs info.paramInfo args
    args.mapM (mkDTExprAux false config)

  match fn with
  | .const c _ =>
    unless root do
      if let some v := toNatLit? e then
        return .lit v
    return .const c (← argDTExprs)
  | .proj s i a =>
    let a ← if isClass (← getEnv) s then pure (.star tmpMVarId) else mkDTExprAux false config a
    return .proj s i a (← argDTExprs)
  | .fvar fvarId =>
    let c ← read
    if let some idx := c.bvars.findIdx? (· == fvarId) then
      return .bvar idx (← argDTExprs)
    else
      if c.unbvars.contains fvarId then
        failure
      else
        return .fvar fvarId (← argDTExprs)
  | .mvar mvarId =>
    if (e matches .app ..) then
      return .star tmpMVarId
    else
      return .star mvarId

  | .lam _ d b _ => checkCache fn fun _ =>
    .lam <$> mkDTExprBinder d b
    <|>
    match starEtaExpanded b 1 with
      | some b => do
        introEtaBVars fn b (mkDTExprAux false config)
      | none => failure

  | .forallE _ d b _ => return .forall (← mkDTExprAux false config d) (← mkDTExprBinder d b)
  | .lit v      => return .lit v
  | .sort _     => return .sort
  | _           => unreachable!

where
  /-- Introduce a bound variable of type `domain` to the context, instantiate it in `e`,
  and then return all encodings of `e` as a `DTExpr` -/
  mkDTExprBinder (domain e : Expr) : M DTExpr := do
    withLocalDeclD `_a domain fun fvar =>
      withReader (fun c => { bvars := fvar.fvarId! :: c.bvars }) do
        mkDTExprAux false config (e.instantiate1 fvar)

end MkDTExpr

/-- return all encodings of `e` as a `DTExpr`. -/
def mkDTExprs (e : Expr) (config : WhnfCoreConfig := {}) : MetaM (List DTExpr) :=
  withReducible do (MkDTExpr.mkDTExprAux true config e |>.run {}).run' {}



-- ## Inserting intro a DiscrTree

/--
If `vs` contains an element `v'` such that `v == v'`, then replace `v'` with `v`.
Otherwise, push `v`.
See issue #2155
Recall that `BEq α` may not be Lawful.
-/
private def insertInArray [BEq α] (vs : Array α) (v : α) : Array α :=
  loop 0
where
  loop (i : Nat) : Array α :=
    if h : i < vs.size then
      if v == vs[i] then
        vs.set ⟨i,h⟩ v
      else
        loop (i+1)
    else
      vs.push v
termination_by loop i => vs.size - i

/-- insert the value `v` at index `keys : Array Key` in a `Trie α`. -/
partial def insertInTrie [BEq α] (keys : Array Key) (v : α) (i : Nat) : Trie α → Trie α
  | .node cs =>
      let k := keys[i]!
      let c := Id.run $ cs.binInsertM
        (fun a b => a.1 < b.1)
        (fun (k', s) => (k', insertInTrie keys v (i+1) s))
        (fun _ => (k, Trie.singleton keys v (i+1)))
        (k, default)
      .node c
  | .values vs =>
      .values (insertInArray vs v)
  | .path ks c => Id.run do
    for n in [:ks.size] do
      let k1 := keys[i+n]!
      let k2 := ks[n]!
      if k1 != k2 then
        let shared := ks[:n]
        let rest := ks[n+1:]
        return .mkPath shared (.mkNode2 k1 (.singleton keys v (i+n+1)) k2 (.mkPath rest c))
    return .path ks (insertInTrie keys v (i + ks.size) c)

/-- insert the value `v` at index `keys : Array Key` in a `DiscrTree α`. -/
def insertInDiscrTree [BEq α] (d : DiscrTree α) (keys : Array Key) (v : α) : DiscrTree α :=
  let k := keys[0]!
  match d.find? k with
  | none =>
    let c := .singleton keys v 1
    d.insert k c
  | some c =>
    let c := insertInTrie keys v 1 c
    d.insert k c

/-- insert the value `v` at index `e : DTExpr` in a `DiscrTree α`. -/
def insertDTExpr [BEq α] (d : DiscrTree α) (e : DTExpr) (v : α) : DiscrTree α :=
  insertInDiscrTree d e.flatten v

/-- insert the value `v` at index `e : Expr` in a `DiscrTree α`. -/
def insert [BEq α] (d : DiscrTree α) (e : Expr) (v : α) (config : WhnfCoreConfig := {})
  : MetaM (DiscrTree α) := do
  let keys ← mkDTExprs e config
  return keys.foldl (insertDTExpr · · v) d



-- ## Matching with a DiscrTree

namespace GetUnify

/-- If `k` is a key in `children`, return the corresponding `Trie α`. Otherwise return `none`. -/
def findKey (children : Array (Key × Trie α)) (k : Key) : Option (Trie α) :=
  (·.2) <$> children.binSearch (k, default) (fun a b => a.1 < b.1)

private structure Context where
  /-- Free variables that came from a lambda or forall binder.
  The list index gives the De Bruijn index. -/
  boundVars : List FVarId := []
  unify : Bool
  config : WhnfCoreConfig

private structure State where
  /-- Score representing how good the match is. -/
  score : Nat := 0
  /-- Metavariable assignments for the `Key.star` patterns in the `DiscrTree`. -/
  assignments : HashMap Nat Expr := {}

private abbrev M := ReaderT Context $ StateListT (State) MetaM

/-- Return all values from `x` in a list, together with their scores. -/
private def M.run (unify : Bool) (config : WhnfCoreConfig) (x : M (Trie α))
  : MetaM (List (Array α × Nat)) :=
  List.map (fun (t, s) => (t.values!, s.score)) <$> (x.run { unify, config }).run {}

/-- increase the score by `n`. -/
private def incrementScore (n : Nat) : M Unit :=
  modify fun s => { s with score := s.score + n }

/-- Log a metavariable assignment in the `State`. -/
private def insertAssignment (n : Nat) (e : Expr) : M Unit :=
  modify fun s => { s with assignments := s.assignments.insert n e }

/-- Return the possible `Trie α` that match with `n` metavariable. -/
partial def skipEntries (t : Trie α) : Nat → M (Trie α)
  | 0      => pure t
  | skip+1 =>
    t.children!.foldr (init := failure) fun (k, c) x =>
      skipEntries c (skip + k.arity) <|> x

/-- Return the possible `Trie α` that match with anything.
We add 1 to the matching score when the key is `.fvar`,
since this pattern is "harder" to match with: it only matches with metavariables. -/
def unifyMVar (children : Array (Key × Trie α)) : M (Trie α) :=
  children.foldr (init := failure) fun (k, c) x => (do
    if k matches .fvar _ _ then
      incrementScore 1
    skipEntries c k.arity
    ) <|> x

/-- Return the possible `Trie α` that come from a `Key.star i` key.
We keep track of the assignments of `Key.star i`, and if there is already an assignment,
we do an `isDefEq` check, without modifying the state. -/
def matchStars (e : Expr) (children : Array (Key × Trie α)) : M (Trie α) := do
  let {assignments, ..} ← get
  let mut result := failure
  /- The `.star` patterns are all at the start of the `Array`,
  so this for loop will find them all. -/
  for (k, c) in children do
    let .star i := k | break
    if let some assignment := assignments.find? i then
      try
        if ← liftMetaM (withoutModifyingState (isDefEq e assignment)) then
          result := (incrementScore 1 *> pure c) <|> result
      catch _ =>
        pure ()
    else
      result := (insertAssignment i e *> pure c) <|> result
  result

/-- An exact match succeeds for keys other than `.star` and `.fvar`,
which are treated separately. -/
private inductive exactMatchResult (α : Type) where
  | mvar
  | fvar
  | exact (result : M (Trie α))
deriving Inhabited

mutual
  /-- Return the possible `Trie α` that match with `e`. -/
  partial def matchExpr (e : Expr) (t : Trie α) : M (Trie α) := do
    let children := t.children!
    match ← exactMatch e (findKey children) false with
      | .mvar => unifyMVar children
      | .fvar => matchStars e children
      | .exact result => result <|> matchStars e children

  /-- Return the possible `Trie α` that match with `e` where the first `Key` matches exactly. -/
  partial def exactMatch (e : Expr) (find? : Key → Option (Trie α)) (root : Bool)
    : M (exactMatchResult α) := do

    let find (k : Key) (x : Trie α → M (Trie α) := pure) (score := 1) : M (exactMatchResult α) :=
      return .exact $ match find? k with
        | none => failure
        | some trie => do
          incrementScore score
          x trie

    let matchArgs (t : Trie α) : M (Trie α) :=
      e.getAppRevArgs.foldrM (fun a c => matchExpr a c) t

    let e ← reduce e (← read).config
    match e.getAppFn with
    | .const c _       =>
      if let some v := guard (!root) *> toNatLit? e then
        find (.lit v)
      else
        find (.const c e.getAppNumArgs) matchArgs

    | .fvar fvarId     =>
      if let some i := (← read).boundVars.findIdx? (· == fvarId) then
        find (.bvar i e.getAppNumArgs) matchArgs
      else
        return .fvar
    | .proj s i a      => find (.proj s i e.getAppNumArgs) (matchExpr a >=> matchArgs)
    | .lit v           => find (.lit v)
    | .mvar _          => return if (← read).unify then .mvar else .fvar
    | .lam _ d b _     => find .lam (score := 0) (matchBinderBody d b)
    | .forallE _ d b _ => find .forall (matchExpr d >=> matchBinderBody d b)
    | _                => find .sort

  /-- Introduce a bound variable of type `domain` to the context, instantiate it in `e`,
  and then return the possible `Trie α` that match `e`. -/
  partial def matchBinderBody (domain e : Expr) (t : Trie α) : M (Trie α) :=
    withLocalDeclD `_a domain fun fvar =>
      withReader (fun c => { c with boundVars := fvar.fvarId! :: c.boundVars }) do
        matchExpr (e.instantiate1 fvar) t

end

end GetUnify

/-- Return the results from the `DiscrTree` that match the given expression,
together with their matching scores.

Each entry of type `Array α × Nat` corresponds to one pattern.

If `unify = false`, then metavariables in `e` are treated as free variables.
This is is for when you don't want the match results to instantiate metavariables in `e`. -/
partial def getMatchWithScore (d : DiscrTree α) (e : Expr) (unify : Bool) (config : WhnfCoreConfig)
  : MetaM (List (Array α × Nat)) :=
  withReducible $ GetUnify.M.run unify config do
    let matchStar := match d.find? (.star 0) with
      | none => failure
      | some c => pure c

    match ← GetUnify.exactMatch e d.find? true with
    /- Matching with an mvar means that we should return all entries of the DiscrTree,
    but that is much too inefficient, so instead we don't return anything.
    TODO: add configuration option for this behaviour. -/
    | .mvar => failure
    | .fvar => matchStar
    | .exact result => result <|> matchStar


variable {m : Type → Type} [Monad m]

/-- Apply a monadic function to the array of values at each node in a `DiscrTree`. -/
partial def Trie.mapArraysM (t : DiscrTree.Trie α) (f : Array α → m (Array β)) :
    m (Trie β) := do
  match t with
  | .node children =>
    return .node (← children.mapM fun (k, t') => do pure (k, ← t'.mapArraysM f))
  | .values vs =>
    return .values (← f vs)
  | .path ks c =>
    return .path ks (← c.mapArraysM f)

/-- Apply a monadic function to the array of values at each node in a `DiscrTree`. -/
def mapArraysM (d : DiscrTree α) (f : Array α → m (Array β)) : m (DiscrTree β) :=
  d.mapM (·.mapArraysM f)

/-- Apply a function to the array of values at each node in a `DiscrTree`. -/
def mapArrays (d : DiscrTree α) (f : Array α → Array β) : DiscrTree β :=
  d.mapArraysM (m := Id) f
