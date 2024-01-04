import Lean.Meta.DiscrTree
import Std.Data.Nat.Init.Lemmas

namespace Lean.Meta

namespace LazyDiscrTree

namespace MatchClone
open DiscrTree

private def tmpMVarId : MVarId := { name := `_discr_tree_tmp }
private def tmpStar := mkMVar tmpMVarId

/--
  Return true iff the argument should be treated as a "wildcard" by the discrimination tree.

  - We ignore proofs because of proof irrelevance. It doesn't make sense to try to
    index their structure.

  - We ignore instance implicit arguments (e.g., `[Add α]`) because they are "morally" canonical.
    Moreover, we may have many definitionally equal terms floating around.
    Example: `Ring.hasAdd Int Int.isRing` and `Int.hasAdd`.

  - We considered ignoring implicit arguments (e.g., `{α : Type}`) since users don't "see" them,
    and may not even understand why some simplification rule is not firing.
    However, in type class resolution, we have instance such as `Decidable (@Eq Nat x y)`,
    where `Nat` is an implicit argument. Thus, we would add the path
    ```
    Decidable -> Eq -> * -> * -> * -> [Nat.decEq]
    ```
    to the discrimination tree IF we ignored the implicit `Nat` argument.
    This would be BAD since **ALL** decidable equality instances would be in the same path.
    So, we index implicit arguments if they are types.
    This setting seems sensible for simplification theorems such as:
    ```
    forall (x y : Unit), (@Eq Unit x y) = true
    ```
    If we ignore the implicit argument `Unit`, the `DiscrTree` will say it is a candidate
    simplification theorem for any equality in our goal.

  Remark: if users have problems with the solution above, we may provide a `noIndexing` annotation,
  and `ignoreArg` would return true for any term of the form `noIndexing t`.
-/
private def ignoreArg (a : Expr) (i : Nat) (infos : Array ParamInfo) : MetaM Bool := do
  if h : i < infos.size then
    let info := infos.get ⟨i, h⟩
    if info.isInstImplicit then
      return true
    else if info.isImplicit || info.isStrictImplicit then
      return not (← isType a)
    else
      isProof a
  else
    isProof a

private partial def pushArgsAux (infos : Array ParamInfo) : Nat → Expr → Array Expr →
    MetaM (Array Expr)
  | i, .app f a, todo => do
    if (← ignoreArg a i infos) then
      pushArgsAux infos (i-1) f (todo.push tmpStar)
    else
      pushArgsAux infos (i-1) f (todo.push a)
  | _, _, todo => return todo

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
        loop (e.getArg! 1)
      else if fName == ``Nat.zero && e.getAppNumArgs == 0 then
        return 0
      else
        failure
    | _ => failure

private def isNatType (e : Expr) : MetaM Bool :=
  return (← whnf e).isConstOf ``Nat

/--
  Return true if `e` is one of the following
  - `Nat.add _ k` where `isNumeral k`
  - `Add.add Nat _ _ k` where `isNumeral k`
  - `HAdd.hAdd _ Nat _ _ k` where `isNumeral k`
  - `Nat.succ _`
  This function assumes `e.isAppOf fName`
-/
private def isOffset (fName : Name) (e : Expr) : MetaM Bool := do
  if fName == ``Nat.add && e.getAppNumArgs == 2 then
    return isNumeral e.appArg!
  else if fName == ``Add.add && e.getAppNumArgs == 4 then
    if (← isNatType (e.getArg! 0)) then return isNumeral e.appArg! else return false
  else if fName == ``HAdd.hAdd && e.getAppNumArgs == 6 then
    if (← isNatType (e.getArg! 1)) then return isNumeral e.appArg! else return false
  else
    return fName == ``Nat.succ && e.getAppNumArgs == 1

/--
  TODO: add hook for users adding their own functions for controlling `shouldAddAsStar`
  Different `DiscrTree` users may populate this set using, for example, attributes.

  Remark: we currently tag "offset" terms as star to avoid having to add special
  support for offset terms.
  Example, suppose the discrimination tree contains the entry
  `Nat.succ ?m |-> v`, and we are trying to retrieve the matches for
  `Expr.lit (Literal.natVal 1) _`.
  In this scenario, we want to retrieve `Nat.succ ?m |-> v`
-/
private def shouldAddAsStar (fName : Name) (e : Expr) : MetaM Bool := do
  isOffset fName e


/--
  Try to eliminate loose bound variables by performing beta-reduction.
  We use this method when processing terms in discrimination trees.
  These trees distinguish dependent arrows from nondependent ones.
  Recall that dependent arrows are indexed as `.other`, but nondependent arrows as `.arrow ..`.
  Motivation: we want to "discriminate" implications and simple arrows in our index.

  Now suppose we add the term `Foo (Nat → Nat)` to our index. The nested arrow appears as
  `.arrow ..`. Then, suppose we want to check whether the index contains
  `(x : Nat) → (fun _ => Nat) x`, but it will fail to retrieve `Foo (Nat → Nat)` because
  it assumes the nested arrow is a dependent one and uses `.other`.

  We use this method to address this issue by beta-reducing terms containing loose bound variables.
  See issue #2232.

  Remark: we expect the performance impact will be minimal.
-/
private def elimLooseBVarsByBeta (e : Expr) : CoreM Expr :=
  Core.transform e
    (pre := fun e => do
      if !e.hasLooseBVars then
        return .done e
      else if e.isHeadBetaTarget then
        return .visit e.headBeta
      else
        return .continue)

private def getKeyArgs (e : Expr) (isMatch root : Bool) (config : WhnfCoreConfig) :
    MetaM (Key × Array Expr) := do
  let e ← reduceDT e root config
  unless root do
    -- See pushArgs
    if let some v := toNatLit? e then
      return (.lit v, #[])
  match e.getAppFn with
  | .lit v         => return (.lit v, #[])
  | .const c _     =>
    if (← getConfig).isDefEqStuckEx && e.hasExprMVar then
      if (← isReducible c) then
        /- `e` is a term `c ...` s.t. `c` is reducible and `e` has metavariables, but it was not
            unfolded.  This can happen if the metavariables in `e` are "blocking" smart unfolding.
           If `isDefEqStuckEx` is enabled, then we must throw the `isDefEqStuck` exception to
           postpone TC resolution.
           Here is an example. Suppose we have
           ```
            inductive Ty where
              | bool | fn (a ty : Ty)


            @[reducible] def Ty.interp : Ty → Type
              | bool   => Bool
              | fn a b => a.interp → b.interp
           ```
           and we are trying to synthesize `BEq (Ty.interp ?m)`
        -/
        Meta.throwIsDefEqStuck
      else if let some matcherInfo := isMatcherAppCore? (← getEnv) e then
        -- A matcher application is stuck is one of the discriminants has a metavariable
        let args := e.getAppArgs
        let start := matcherInfo.getFirstDiscrPos
        for arg in args[ start : start + matcherInfo.numDiscrs ] do
          if arg.hasExprMVar then
            Meta.throwIsDefEqStuck
      else if (← isRec c) then
        /- Similar to the previous case, but for `match` and recursor applications. It may be stuck
           (i.e., did not reduce) because of metavariables. -/
        Meta.throwIsDefEqStuck
    let nargs := e.getAppNumArgs
    return (.const c nargs, e.getAppRevArgs)
  | .fvar fvarId   =>
    let nargs := e.getAppNumArgs
    return (.fvar fvarId nargs, e.getAppRevArgs)
  | .mvar mvarId   =>
    if isMatch then
      return (.other, #[])
    else do
      let ctx ← read
      if ctx.config.isDefEqStuckEx then
        /-
          When the configuration flag `isDefEqStuckEx` is set to true,
          we want `isDefEq` to throw an exception whenever it tries to assign
          a read-only metavariable.
          This feature is useful for type class resolution where
          we may want to notify the caller that the TC problem may be solvable
          later after it assigns `?m`.
          The method `DiscrTree.getUnify e` returns candidates `c` that may "unify" with `e`.
          That is, `isDefEq c e` may return true. Now, consider `DiscrTree.getUnify d (Add ?m)`
          where `?m` is a read-only metavariable, and the discrimination tree contains the keys
          `HadAdd Nat` and `Add Int`. If `isDefEqStuckEx` is set to true, we must treat `?m` as
          a regular metavariable here, otherwise we return the empty set of candidates.
          This is incorrect because it is equivalent to saying that there is no solution even if
          the caller assigns `?m` and try again. -/
        return (.star, #[])
      else if (← mvarId.isReadOnlyOrSyntheticOpaque) then
        return (.other, #[])
      else
        return (.star, #[])
  | .proj s i a .. =>
    let nargs := e.getAppNumArgs
    return (.proj s i nargs, #[a] ++ e.getAppRevArgs)
  | .forallE _ d b _ =>
    -- See comment at elimLooseBVarsByBeta
    let b ← if b.hasLooseBVars then elimLooseBVarsByBeta b else pure b
    if b.hasLooseBVars then
      return (.other, #[])
    else
      return (.arrow, #[d, b])
  | _ =>
    return (.other, #[])

/- Copy of Lean.Meta.DiscrTree.getMatchKeyArgs -/
private abbrev getMatchKeyArgs (e : Expr) (root : Bool) (config : WhnfCoreConfig) :
    MetaM (Key × Array Expr) :=
  getKeyArgs e (isMatch := true) (root := root) (config := config)

end MatchClone

export DiscrTree (Key)

/--
Stack of subexpressions to process to generate key.
-/
def ExprRest := Array Expr
  deriving Inhabited

/--
An unprocessed entry in the lazy discriminator tree.
-/
abbrev LazyEntry α := ExprRest × ((LocalContext × LocalInstances) × α)

/--
Index identifying trie in a discriminator tree.
-/
@[reducible]
def TrieIndex := Nat

/--
Discrimination tree trie. See `LazyDiscrTree`.
-/
structure Trie (α : Type) where
  node ::
    /-- Values for matches ending at this trie. -/
    values : Array α
    /-- Index of trie matching star. -/
    star : TrieIndex
    /-- Following matches based on key of trie. -/
    children : HashMap Key TrieIndex
    /-- Lazy entries at this trie that are not processed. -/
    pending : Array (LazyEntry α)
  deriving Inhabited

/-- Push lazy entry to trie. -/
private def Trie.pushPending : Trie α  → LazyEntry α → Trie α
| .node vs star cs p, e => .node vs star cs (p.push e)

end LazyDiscrTree

/--
`LazyDiscrTree` is a variant of the discriminator tree datatype
`DiscrTree` in Lean core that is designed to be efficiently
initializable with a large number of patterns.  This is useful
in contexts such as searching an entire Lean environment for
expressions that match a pattern.

Lazy discriminator trees achieve good performance by minimizing
the amount of work that is done up front to build the discriminator
tree.  When first adding patterns to the tree, only the root
discriminator key is computed and processing the remaining
terms is deferred until demanded by a match.
-/
structure LazyDiscrTree (α : Type) where
  /-- Configuration for normalization. -/
  config : Lean.Meta.WhnfCoreConfig := {}
  /-- Backing array of trie entries.  Should be owned by this trie. -/
  array : Array (LazyDiscrTree.Trie α) := #[default]
  /-- Map from disriminator trie roots to the index. -/
  root : Lean.HashMap LazyDiscrTree.Key LazyDiscrTree.TrieIndex := {}

namespace LazyDiscrTree

open Lean Elab Meta

instance : Inhabited (LazyDiscrTree α) where
  default := {}

/-- Return true if trie is empty. -/
def isEmpty (t:LazyDiscrTree α) : Bool := t.array.size ≤ 1

open Lean.Meta.DiscrTree (mkNoindexAnnotation hasNoindexAnnotation reduceDT)

/--
Specialization of Lean.Meta.DiscrTree.pushArgs
-/
private def pushArgs (root : Bool) (todo : ExprRest) (e : Expr) (config : WhnfCoreConfig) :
    MetaM (Key × ExprRest) := do
  if hasNoindexAnnotation e then
    return (.star, todo)
  else
    let e ← reduceDT e root config
    let fn := e.getAppFn
    let push (k : Key) (nargs : Nat) (todo : ExprRest) : MetaM (Key × ExprRest) := do
      let info ← getFunInfoNArgs fn nargs
      let todo ← MatchClone.pushArgsAux info.paramInfo (nargs-1) e todo
      return (k, todo)
    match fn with
    | .lit v     =>
      return (.lit v, todo)
    | .const c _ =>
      unless root do
        if let some v := MatchClone.toNatLit? e then
          return (.lit v, todo)
        if (← MatchClone.shouldAddAsStar c e) then
          return (.star, todo)
      let nargs := e.getAppNumArgs
      push (.const c nargs) nargs todo
    | .proj s i a =>
      /-
      If `s` is a class, then `a` is an instance. Thus, we annotate `a` with `no_index` since we do
      not index instances. This should only happen if users mark a class projection function as
      `[reducible]`.

      TODO: add better support for projections that are functions
      -/
      let a := if isClass (← getEnv) s then mkNoindexAnnotation a else a
      let nargs := e.getAppNumArgs
      push (.proj s i nargs) nargs (todo.push a)
    | .fvar _fvarId   =>
--      let bi ← fvarId.getBinderInfo
--      if bi.isInstImplicit then
--        return (.other, todo)
--      else
      return (.star, todo)
    | .mvar mvarId   =>
      if mvarId == MatchClone.tmpMVarId then
        -- We use `tmp to mark implicit arguments and proofs
        return (.star, todo)
      else
        failure
    | .forallE _ d b _ =>
      -- See comment at elimLooseBVarsByBeta
      let b ← if b.hasLooseBVars then MatchClone.elimLooseBVarsByBeta b else pure b
      if b.hasLooseBVars then
        return (.other, todo)
      else
        return (.arrow, (todo.push d).push b)
    | _ =>
      return (.other, todo)

/-- Initial capacity for key and todo vector. -/
private def initCapacity := 8

/--
Adds a key and
-/
def addEntry' : LazyDiscrTree α → LocalContext × LocalInstances → Key → Array Expr → α →
    LazyDiscrTree α
| { config := c, array := a, root := r }, lctx, k, todo, v =>
  let rest := (todo, lctx, v)
  match r.find? k with
  | none =>
    let r := r.insert k a.size
    let a := a.push (.node #[] 0 {} #[rest])
    { config := c, array := a, root := r }
  | some idx =>
    let a := a.modify idx fun t => t.pushPending rest
    { config := c, array := a, root := r }

/--
Get the root key of an expression using the specified config.
-/
def rootKey' (cfg: WhnfCoreConfig) (e : Expr) : MetaM (Key × Array Expr) :=
  pushArgs true (Array.mkEmpty initCapacity) e cfg

/--
Get the root key of an expression using the config from the lazy dicriminator tree.
-/
def rootKey (cfg: WhnfCoreConfig) (lctx : LocalContext × LocalInstances) (e : Expr) :
    MetaM (Key × Array Expr) :=
  withReducible $ withLCtx lctx.1 lctx.2 $ rootKey' cfg e

/--
Adds an association between the given expression.  Free variables are used to
denote paramters that may be matched against.
-/
def addEntry (d : LazyDiscrTree α) (lctx : LocalContext × LocalInstances) (type : Expr) (v : α) :
    MetaM (LazyDiscrTree α) := do
  let (k, todo) ← rootKey d.config lctx type
  pure $ addEntry' d lctx k todo v

private partial def mkPathAux (root : Bool) (todo : Array Expr) (keys : Array Key)
    (config : WhnfCoreConfig) : MetaM (Array Key) := do
  if todo.isEmpty then
    return keys
  else
    let e    := todo.back
    let todo := todo.pop
    let (k, todo) ← pushArgs root todo e config
    mkPathAux false todo (keys.push k) config

/--
Create a path from an expression.

This differs from Lean.Meta.DiscrTree.mkPath in that the expression
should uses free variables rather than meta-variables for holes.
-/
def mkPath (e : Expr) (config : WhnfCoreConfig) : MetaM (Array Key) := do
  let todo : Array Expr := .mkEmpty initCapacity
  let keys : Array Key := .mkEmpty initCapacity
  mkPathAux (root := true) (todo.push e) keys config

/- Monad for finding matches while resolving deferred patterns. -/
@[reducible]
private def MatchM α := ReaderT WhnfCoreConfig (StateRefT (Array (Trie α)) MetaM)

private def runMatch (m : MatchM α β) (d : LazyDiscrTree α) : MetaM (β × LazyDiscrTree α) := do
  let { config := c, array := a, root := r } := d
  let (result, a) ← withReducible $ (m.run c).run a
  pure (result, { config := c, array := a, root := r})

private def setTrie (i : TrieIndex) (v : Trie α) : MatchM α Unit :=
  modify (·.set! i v)

private def modifyTrie (i:TrieIndex) (e : LazyEntry α) : MatchM α Unit :=
  modify (·.modify i (·.pushPending e))

private def newTrie [Monad m] [MonadState (Array (Trie α)) m] (e : LazyEntry α) : m TrieIndex := do
  modifyGet fun a => let sz := a.size; (sz, a.push (.node #[] 0 {} #[e]))

private partial def processEntries (config : WhnfCoreConfig)
    (values : Array α)
    (starIdx : TrieIndex)
    (children : HashMap Key TrieIndex)
    (entries : Array (LazyEntry α)) :
    MatchM α (Array α × TrieIndex × HashMap Key TrieIndex) := do
  if h : entries.size = 0 then
    pure (values, starIdx, children)
  else
    let p : entries.size - 1 < entries.size := Nat.sub_lt (Nat.pos_of_ne_zero h) (Nat.le_refl _)
    let (todo, lctx, v) := entries[entries.size - 1]
    let entries := entries.pop
    if todo.isEmpty then
      let values := values.push v
      processEntries config values starIdx children entries
    else
      let e    := todo.back
      let todo := todo.pop
      let (k, todo) ← withLCtx lctx.1 lctx.2 $ pushArgs false todo e config
      if k == .star then
        if starIdx = 0 then
          let starIdx ← newTrie (todo, lctx, v)
          processEntries config values starIdx children entries
        else
          modifyTrie starIdx (todo, lctx, v)
          processEntries config values starIdx children entries
      else
        match children.find? k with
        | none =>
          let children := children.insert k (← newTrie (todo, lctx, v))
          processEntries config values starIdx children entries
        | some idx =>
          modifyTrie idx (todo, lctx, v)
          processEntries config values starIdx children entries

private def evalNode (c : TrieIndex) :
    MatchM α (Array α × TrieIndex × HashMap Key TrieIndex) := do
  let .node vs star cs pending := (←get).get! c
  if pending.size = 0 then
    pure (vs, star, cs)
  else
    let config ← read
    setTrie c default
    let (vs, star, cs) ← processEntries config vs star cs pending
    setTrie c <| .node vs star cs #[]
    pure (vs, star, cs)

/--
Return the information about the trie at the given idnex.

Used for internal debugging purposes.
-/
def getTrie (d : LazyDiscrTree α) (idx : TrieIndex) :
    MetaM ((Array α × TrieIndex × HashMap Key TrieIndex) × LazyDiscrTree α) :=
  runMatch (evalNode idx) d

private structure MatchResult (α : Type) where
  elts : Array (Array α) := #[]

private def MatchResult.push (r : MatchResult α) (a : Array α) : MatchResult α :=
  if a.isEmpty then r else ⟨r.elts.push a⟩

private partial def MatchResult.toArrayRev (mr : MatchResult α) : Array α :=
    loop (Array.mkEmpty n) mr.elts
  where n := mr.elts.foldl (fun n a => n + a.size) 0
        loop (r : Array α) a :=
          if a.isEmpty then
            r
          else
            loop (r ++ a.back) a.pop

private partial def getMatchLoop (todo : Array Expr) (c : TrieIndex) (result : MatchResult α) :
    MatchM α (MatchResult α) := do
  let (vs, star, cs) ← evalNode c
  if todo.isEmpty then
    return result.push vs
  else if star == 0 && cs.isEmpty then
    return result
  else
    let e     := todo.back
    let todo  := todo.pop
    let (k, args) ← MatchClone.getMatchKeyArgs e (root := false) (←read)
    /- We must always visit `Key.star` edges since they are wildcards.
        Thus, `todo` is not used linearly when there is `Key.star` edge
        and there is an edge for `k` and `k != Key.star`. -/
    let visitStar (result : MatchResult α) : MatchM α (MatchResult α) :=
      if star != 0 then
        getMatchLoop todo star result
      else
        return result
    let visitNonStar (k : Key) (args : Array Expr) (result : MatchResult α) :=
      match cs.find? k with
      | none   => return result
      | some c => getMatchLoop (todo ++ args) c result
    let result ← visitStar result
    match k with
    | .star  => return result
    /-
      Note: dep-arrow vs arrow
      Recall that dependent arrows are `(Key.other, #[])`, and non-dependent arrows are
      `(Key.arrow, #[a, b])`.
      A non-dependent arrow may be an instance of a dependent arrow (stored at `DiscrTree`).
      Thus, we also visit the `Key.other` child.
    -/
    | .arrow => visitNonStar .other #[] (← visitNonStar k args result)
    | _      => visitNonStar k args result

private def getStarResult (root : Lean.HashMap Key TrieIndex) : MatchM α (MatchResult α) :=
  match root.find? .star with
  | none =>
    pure <| {}
  | some idx => do
    let (vs, _) ← evalNode idx
    pure <| ({} : MatchResult α).push vs

private def getMatchRoot (r : Lean.HashMap Key TrieIndex) (k : Key) (args : Array Expr)
    (result : MatchResult α) : MatchM α (MatchResult α) :=
  match r.find? k with
  | none => pure result
  | some c => getMatchLoop args c result

/--
  Find values that match `e` in `d`.
-/
def getMatchCore (root : Lean.HashMap Key TrieIndex) (e : Expr) : MatchM α (MatchResult α) :=
  withReducible do
    let result ← getStarResult root
    let (k, args) ← MatchClone.getMatchKeyArgs e (root := true) (←read)
    match k with
    | .star  => return result
    /- See note about "dep-arrow vs arrow" at `getMatchLoop` -/
    | .arrow =>
      getMatchRoot root k args (←getMatchRoot root .other #[] result)
    | _ =>
      getMatchRoot root k args result

/--
  Find values that match `e` in `d`.
-/
def getMatch (d : LazyDiscrTree α) (e : Expr) : MetaM (Array α × LazyDiscrTree α) :=
  runMatch (MatchResult.toArrayRev <$> getMatchCore d.root e) d
