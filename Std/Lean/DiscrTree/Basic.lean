/-
Copyright (c) 2023 J. W. Gerbscheid. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: J. W. Gerbscheid
-/
import Std.Lean.DiscrTree.Init.Basic
import Std.Data.ListState
import Std.Data.List.Basic
import Lean.Meta

/-!
This file is a modification of DiscrTree.lean in Lean, with some parts removed and some new features added.
I document only what is different from that file.

We define discrimination trees for the purpose of unifying local expressions with library results.

These are the features that are not in Lean's discrimination trees:

- The constructor `Key.fvar` and `Key.star` now take a `Nat` as an argument, as an identifier.
  For example, the library pattern `a+a` is encoded as `[⟨Hadd.hadd, 6⟩, *0, *0, *0, *1, *2, *2]`.
  `*0` corresponds to the type of `a`, `*1` to the `Hadd` instance, and `*2` to `a`.
  This means that it will only match an expression `x+y` if `x` is definitionally equal to `y`.

  `Key.fvar` is used in lemmas like `Nat.exists_prime_and_dvd {n : ℕ} (hn : n ≠ 1) : ∃ p, Prime p ∧ p ∣ n`,
  where the part `Prime p` gets the pattern `[⟨Nat.Prime, 1⟩, .fvar 0 0]`.
  the first argument of `Key.fvar` is the identifier, and the second argument is the arity.

  If a discrimination tree is built locally, there is a need for a `Key.fvar` that takes an `FVarId`
  as an idenitifier, which is what the DiscrTree defined in Lean does, but this is of no use for us.

- The constructors `Key.lam`, `Key.forall` and `Key.bvar` have been introduced in order to allow for patterns under binders.
  For example, this allows for more specific matching with the left hand side of
  `Finset.sum_range_id (n : ℕ) : ∑ i in range n, i = n * (n - 1) / 2`

- We keep track of a matching score of a unification.
  This score represent the number of keys that had to be the same for the unification to succeed.
  For example, matching `(1 + 2) + 3` with `add_comm` gives a score of 3,
  since the pattern of commutativity is [⟨Hadd.hadd, 6⟩, *0, *0, *0, *1, *2, *3],
  so matching `⟨Hadd.hadd, 6⟩` gives 1 point,
  and matching `*0` two times after its first appearence gives another 2 points.
  Similarly, matching it with `add_assoc` gives a score of 7.

  TODO?: the third type parameter of `Hadd.hadd` is an outparam, so its matching should not be counted to the score.

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

namespace Std.DiscrTree

open Lean Meta


/-- The discrimination tree ignores instance implicit arguments and proofs.
   We use the following auxiliary id as a "mark". -/
private def tmpMVarId : MVarId := { name := `_discr_tree_tmp }
private def tmpStar : Expr := mkMVar tmpMVarId


/-- this state is used to turn the indexing by `MVarId` and `FVarId` in `DTExpr` into indexing by `Nat` in `Key`. -/
private structure Flatten.State where
  stars : Array MVarId := #[]
  fvars : Array FVarId := #[]

private def getFVar (fvarId : FVarId) : StateM Flatten.State Nat :=
  modifyGet fun s =>
  match s.fvars.findIdx? (· == fvarId) with
  | some idx => (idx, s)
  | none => (s.fvars.size, { s with fvars := s.fvars.push fvarId })

private def getStar (mvarId : MVarId) : StateM Flatten.State Nat :=
  modifyGet fun s =>
  if mvarId != tmpMVarId then
    if let some idx := s.stars.findIdx? (· == mvarId) then
      (idx, s)
    else
      (s.stars.size, { s with stars := s.stars.push mvarId })
  else
    (s.stars.size, { s with stars := s.stars.push mvarId })

private partial def DTExpr.flattenAux (todo : Array Key) : DTExpr → StateM Flatten.State (Array Key)
  | .const n args =>   args.foldlM (init := todo.push (.const n args.size)) flattenAux
  | .fvar i args => do args.foldlM (init := todo.push (.fvar (← getFVar i) args.size)) flattenAux
  | .bvar i args =>    args.foldlM (init := todo.push (.bvar i args.size)) flattenAux
  | .star i => return todo.push (.star (← getStar i))
  | .lit l => return todo.push (.lit l)
  | .sort => return todo.push .sort
  | .lam b => flattenAux (todo.push .lam) b
  | .«forall» d b => do flattenAux (← flattenAux (todo.push .forall) d) b
  | .proj n i e args => do args.foldlM (init := ← flattenAux (todo.push (.proj n i args.size)) e) flattenAux

/-- given a `DTExpr`, return the linearized encoding in terms of `Key`, which is used for `DiscrTree` indexing. -/
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



private def mkNoindexAnnotation (e : Expr) : Expr :=
  mkAnnotation `noindex e

private def hasNoindexAnnotation (e : Expr) : Bool :=
  annotation? `noindex e |>.isSome


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


namespace MkPath

private structure Context where
  /-- Free variables that have been introduced from a lambda. -/
  bvars : List FVarId := []
  /-- Free variables that come from a lambda that has been removed via η-reduction. -/
  unbvars : List FVarId := []

private abbrev M := ReaderT Context $ ListStateT (AssocList Expr DTExpr) MetaM

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

private partial def mkPathAux (root : Bool) (config : WhnfCoreConfig) (e : Expr) : M DTExpr := do
  let e ← reduce e config
  Expr.withApp e fun fn args => do
  let argPaths : M (Array DTExpr) := do
    let info ← getFunInfoNArgs fn args.size
    let args ← ignoreArgs info.paramInfo args
    args.mapM (mkPathAux false config)

  match fn with
  | .const c _ =>
    unless root do
      if let some v := toNatLit? e then
        return .lit v
    return .const c (← argPaths)
  | .proj s i a =>
    let a ← if isClass (← getEnv) s then pure (.star tmpMVarId) else mkPathAux false config a
    return .proj s i a (← argPaths)
  | .fvar fvarId =>
    let c ← read
    if let some idx := c.bvars.findIdx? (· == fvarId) then
      return .bvar idx (← argPaths)
    else
      if c.unbvars.contains fvarId then
        failure
      else
        return .fvar fvarId (← argPaths)
  | .mvar mvarId =>
    if (e matches .app ..) then
      return .star tmpMVarId
    else
      return .star mvarId

  | .lam _ d b _ => checkCache fn fun _ =>
    .lam <$> mkPathBinder d b
    <|>
    match starEtaExpanded b 1 with
      | some b => do
        introEtaBVars fn b (mkPathAux false config)
      | none => failure

  | .forallE _ d b _ => return .forall (← mkPathAux false config d) (← mkPathBinder d b)
  | .lit v      => return .lit v
  | .sort _     => return .sort
  | _           => unreachable!

where
  mkPathBinder (domain body : Expr) : M DTExpr := do
    withLocalDeclD `_a domain fun fvar =>
      withReader (m := M) (fun c => { bvars := fvar.fvarId! :: c.bvars }) $
        mkPathAux false config (body.instantiate1 fvar)

end MkPath

/-- return all encodings of `e` as a `DTExpr`. -/
def mkDTExprs (e : Expr) (config : WhnfCoreConfig := {}) : MetaM (List DTExpr) :=
  withReducible do (MkPath.mkPathAux true config e |>.run {}).run' {}



-- **Inserting intro a DiscrTree**

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
def insert [BEq α] (d : DiscrTree α) (e : Expr) (v : α) (config : WhnfCoreConfig := {}) : MetaM (DiscrTree α) := do
  let keys ← mkDTExprs e config
  return keys.foldl (insertDTExpr · · v) d



-- **Retrieving from a DiscrTree**

namespace GetUnify

def findKey (cs : Array (Key × Trie α)) (k : Key) : Option (Trie α) :=
  (·.2) <$> cs.binSearch (k, default) (fun a b => a.1 < b.1)

private structure Context where
  boundVars : List FVarId := []
  config : WhnfCoreConfig

private structure State where
  score : Nat := 0
  assignments : HashMap Nat Expr := {}

private abbrev M := ReaderT Context $ ListStateT (State) MetaM

private def M.run (config : WhnfCoreConfig) (x : M (Trie α)) : MetaM (List (Array α × Nat)) :=
  (List.map fun (t, s) => (t.values!, s.score)) <$> (x.run {config}).run {}

def incrementScore (n : Nat) : M Unit :=
  modify fun s => { s with score := s.score + n }

def insertAssignment (n : Nat) (e : Expr) : M Unit :=
  modify fun s => { s with assignments := s.assignments.insert n e }

partial def skipEntries (t : Trie α) : Nat → M (Trie α)
  | 0      => pure t
  | skip+1 =>
    t.children!.foldr (init := failure) fun (k, c) x => (do skipEntries c (skip + k.arity)) <|> x

def matchMVar (children : Array (Key × Trie α)) : M (Trie α) :=
  children.foldr (init := failure) (fun (k, c) x => (do
    if k matches .fvar .. then
      incrementScore 1
    skipEntries c k.arity
    ) <|> x)

def matchStars (e : Expr) (children : Array (Key × Trie α)) : M (Trie α) := do
  let {assignments, ..} ← get
  let mut result := failure
  for (k, c) in children do
    match k with
    | .star i =>
      match assignments.find? i with
      | some assignment =>
        try
          /- it would be nicer if we could keep the `isDefEq` state,
          but if we do so the state will leak to alternative cases, which is a problem. -/
          if ← liftMetaM (withoutModifyingState (isDefEq e assignment)) then
            result := (pure c) <|> result
        catch _ =>
          pure ()
      | none =>
        result := (insertAssignment i e *> pure c) <|> result
    | _ => break
  result

private inductive exactMatchResult (α : Type) where
  | mvar
  | fvar
  | exact (result : M (Trie α))
deriving Inhabited

mutual
  partial def matchExpr (e : Expr) (t : Trie α) : M (Trie α) := do
    let e ← reduce e (← read).config
    let children := t.children!
    match exactMatch e (← read).boundVars (findKey children) false with
      | .mvar => matchMVar children
      | .fvar => matchStars e children
      | .exact result => result <|> matchStars e children

  partial def exactMatch (e : Expr) (boundVars : List FVarId) (find? : Key → Option (Trie α)) (root : Bool) : exactMatchResult α :=
    let find (k : Key) (x : Trie α → M (Trie α)) (score := 1) : exactMatchResult α := .exact do
      match find? k with
        | none => failure
        | some trie => incrementScore score; x trie

    match e.getAppFn with
    | .const c _       =>
      if let some v := guard (!root) *> toNatLit? e then
        find (.lit v) pure
      else
        find (.const c e.getAppNumArgs) (matchArgs e)

    | .fvar fvarId     =>
      if let some i := boundVars.findIdx? (· == fvarId) then
        find (.bvar i e.getAppNumArgs) (matchArgs e)
      else
        .fvar
    | .proj s i a      => find (.proj s i e.getAppNumArgs) (matchExpr a >=> matchArgs e)
    | .lit v           => find (.lit v) pure
    | .mvar _          => .mvar
    | .lam _ d b _     => find .lam    (matchBoundExpr d b) (score := 0)
    | .forallE _ d b _ => find .forall (matchExpr d >=> matchBoundExpr d b)
    | _                => find .sort   pure


  partial def matchArgs (e : Expr) (t : Trie α) : M (Trie α) :=
    e.getAppRevArgs.foldrM (fun a c => matchExpr a c) t

  partial def matchBoundExpr (domain body : Expr) (t : Trie α) : M (Trie α) :=
    withLocalDeclD `_a domain fun fvar =>
      withReader (fun c => { c with boundVars := fvar.fvarId! :: c.boundVars }) do
        matchExpr (body.instantiate1 fvar) t

end

/-- return the results from the DiscrTree that match the given expression, together with their matching scores. -/
partial def getUnifyWithScore (d : DiscrTree α) (e : Expr) (config : WhnfCoreConfig) : MetaM (List (Array α × Nat)) :=
  withReducible $ M.run config do
    let e ← reduce e config
    let matchStar := match d.find? (.star 0) with
      | none => failure
      | some c => pure c

    match exactMatch e [] (d.find?) true with
    | .mvar => failure
    | .fvar => matchStar
    | .exact result => result <|> matchStar

end GetUnify


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
  d.mapM (fun t => t.mapArraysM f)

/-- Apply a function to the array of values at each node in a `DiscrTree`. -/
def mapArrays (d : DiscrTree α) (f : Array α → Array β) : DiscrTree β :=
  d.mapArraysM fun A => (pure (f A) : Id (Array β))
