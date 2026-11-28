/-
Copyright (c) 2026 Harald Nordgren. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Harald Nordgren
-/
module

public meta import Batteries.Tactic.Lint.Basic
public meta import Lean.Meta.Instances
public meta import Lean.Meta.WHNF
public meta import Lean.Util.PtrSet
public meta import Std.Data.HashSet.Basic

public meta section

/-!
# Dead weight in a development

Given the theorems that a development is about (the *roots*), `Batteries.DeadWeight.analyze` finds
the parts of the development that the roots do not use:

* modules and declarations that no root reaches,
* structure fields that nothing reachable reads,
* propositions and predicates that are always true and have no alternative,
* other reachable definitions that ignore every argument.

This is a property of the whole environment. In particular, a structure field cannot be judged
where it is declared, because nothing has used it yet. So this is not a linter. The command-line
interface is `lake exe deadWeight`.

## Predicates without an alternative

A predicate that is always true, such as `def anyShape : Nat → Prop := fun _ => True`, can be
deliberate: it is the natural choice for a parameter that some other part of the development fills
with a real condition. It is dead weight if nothing but predicates that are always true ever reaches
the parameters that it fills. Then these parameters can be removed, and so can the predicate.

To find out, the analysis follows predicates from the arguments of constants to their parameters,
and through structure fields. It takes a value to be always true if it has no content, see
`isAlwaysTrue`. Where it cannot follow a predicate, such as through a `match` or a partial
application, it assumes that there is an alternative.

The same holds for propositions, such as `def NoCondition : Prop := True`. These are also dead
weight if they are not an argument at all, for example if they are only a hypothesis.

## Limitations

The analysis looks at compiled terms, so its results are candidates. Before removing one, check that
the development still builds without it. Dead declarations can refer to each other and to dead
modules, so remove them together.

* A declaration can be absent from every term and still be needed during elaboration: a lemma that
  `simp [...]` tries, an instance that is tried and discarded, or code that a macro or tactic runs.
* A structure that is destructured (by `match`, `obtain`, or a recursor) has all of its fields bound
  at once. The analysis does not track which of the bound variables are used, and reports the fields
  of such a structure separately, as inconclusive.
* A field that is read only to build a field that nothing reads counts as read.
* A lemma that is general on purpose, but is used only once and for a predicate that is always true,
  looks like one with a parameter that can be removed.
* For programs, the analysis follows the logical definitions. It does not see the bodies of
  `partial` definitions, which are opaque, or code that only `implemented_by`, `extern` or `csimp`
  refer to.
* If the proof of a theorem is not loaded, what it uses looks dead. `import` in a file that uses
  `module` has this effect. `lake exe deadWeight` loads the private data of all modules, so it does
  see the proofs, and it reports a theorem without one as an unexpected axiom.
* A definition can be reachable without its value mattering. The way to find out is to replace it by
  a variable and to check whether the proof still goes through. The analysis does not do this.
-/

namespace Batteries.DeadWeight
open Lean Meta

/-- The constants and the primitive projections that occur in some terms. -/
structure Uses where
  /-- The constants. -/
  consts : Std.HashSet Name := {}
  /-- The primitive projections, as the name of the structure and the index of the field. -/
  projs : Std.HashSet (Name × Nat) := {}
  deriving Inhabited

namespace Uses

/-- The implementation of `Uses.addExpr`. -/
private unsafe def addExprUnsafe (uses : Uses) (e : Expr) : Uses :=
  (go e |>.run (mkPtrSet, uses)).2.2
where
  /-- Visits each shared subterm of `e` once. -/
  go (e : Expr) : StateM (PtrSet Expr × Uses) Unit := do
    if (← get).1.contains e then return
    modify fun (seen, uses) => (seen.insert e, uses)
    match e with
    | .forallE _ d b _ | .lam _ d b _ => go d; go b
    | .letE _ t v b _ => go t; go v; go b
    | .app f a => go f; go a
    | .mdata _ b => go b
    | .proj s i b =>
      modify fun (seen, uses) =>
        (seen, { uses with consts := uses.consts.insert s, projs := uses.projs.insert (s, i) })
      go b
    | .const c _ => modify fun (seen, uses) => (seen, { uses with consts := uses.consts.insert c })
    | _ => return

/-- Adds the constants and primitive projections in `e`. -/
@[implemented_by addExprUnsafe]
opaque addExpr (uses : Uses) (e : Expr) : Uses

/-- Adds the constants and primitive projections that `info` refers to. -/
def addConstantInfo (uses : Uses) (info : ConstantInfo) : Uses :=
  let uses := uses.addExpr info.type
  match info with
  -- A recursor is not part of the inductive type, but of the terms that use it.
  | .inductInfo val => { uses with consts := uses.consts.insertMany (val.all ++ val.ctors) }
  | .ctorInfo val => { uses with consts := uses.consts.insert val.induct }
  | .recInfo val => val.rules.foldl (init := uses) fun uses rule => uses.addExpr rule.rhs
  | info => match info.value? (allowOpaque := true) with
    | some value => uses.addExpr value
    | none => uses

end Uses

/-- The constants that `roots` reach, and the primitive projections in those constants. -/
def reach (env : Environment) (roots : Array Name) : Uses := Id.run do
  let mut seen : Std.HashSet Name := .ofArray roots
  let mut projs := {}
  let mut todo := roots
  repeat
    let some c := todo.back? | break
    todo := todo.pop
    let some info := env.find? c | continue
    let uses := Uses.addConstantInfo { projs } info
    projs := uses.projs
    for c in uses.consts do
      unless seen.contains c do
        seen := seen.insert c
        todo := todo.push c
  return { consts := seen, projs }

/-- A structure field that nothing reachable reads. -/
structure UnreadField where
  /-- The name of the structure. -/
  structName : Name
  /-- The name of the field. -/
  fieldName : Name
  /-- Whether the structure is destructured, so that the field may be read after all. -/
  destructured : Bool

/-- The results of `analyze`. Each array is sorted by name. -/
structure Report where
  /-- The number of constants that the roots reach. -/
  numReached : Nat := 0
  /-- The number of declarations in scope. -/
  numDecls : Nat := 0
  /-- The number of declarations in scope that the roots do not reach. -/
  numDead : Nat := 0
  /-- The modules that contain declarations in scope, none of which the roots reach. -/
  deadModules : Array Name := #[]
  /-- The declarations in scope that the roots do not reach, except for those in `deadModules`. -/
  deadDecls : Array Name := #[]
  /-- The fields of reachable structures in scope that nothing reachable reads. -/
  unreadFields : Array UnreadField := #[]
  /-- The reachable predicates in scope that are always true and have no alternative, and the
  constants whose parameters they fill. -/
  vacuousPredicates : Array (Name × Array Name) := #[]
  /-- The other reachable predicates in scope that are constant, and what is known about them. -/
  constantPredicates : Array (Name × MessageData) := #[]
  /-- The other reachable definitions in scope that ignore all of their arguments. -/
  constantFunctions : Array Name := #[]
  /-- The reachable axioms. If the body of a theorem is not loaded, it shows up here. -/
  axioms : Array Name := #[]

/-- Runs `x` with a resource limit, and returns `default` if it fails or exceeds the limit. This
keeps a single term from ending a run on a large development. -/
def guarded (default : α) (x : MetaM α) : MetaM α :=
  tryCatchRuntimeEx
    (withTheReader Core.Context (fun ctx => { ctx with maxHeartbeats := 20000 * 1000 }) <|
      withCurrHeartbeats x)
    fun ex => if ex.isInterrupt then throw ex else return default

/-! ### Constant predicates -/

/--
Whether the proposition `prop` is always true because it has no content, if this holds for all
values of the predicates `atoms`. After unfolding at most `fuel` definitions and constructors, it is
built from `True` and values of `atoms` with `∀`, `→` and inductive propositions that have a
constructor for all indices and from hypotheses that are always true, such as `∧`.

This does not include all propositions that are easy to prove. For example, `∀ n : Nat, n + 0 = n`
is true by `rfl`, but a proof of it can be used.
-/
partial def isAlwaysTrue (atoms : Array Expr) (prop : Expr) (fuel : Nat := 16) : MetaM Bool := do
  let prop ← whnfCore prop
  if prop.isTrue then return true
  let isValueOf (atom : Expr) : Bool :=
    mkAppN prop.getAppFn (prop.getAppArgs.extract 0 atom.getAppNumArgs) == atom
  if atoms.any isValueOf then return true
  let fuel + 1 := fuel | return false
  if prop.isForall then
    return ← forallTelescope prop fun _ prop => isAlwaysTrue atoms prop fuel
  let .const c us := prop.getAppFn | return false
  match (← getEnv).find? c with
  | some (.inductInfo val) =>
    let params := prop.getAppArgs.extract 0 val.numParams
    let indices := prop.getAppArgs.extract val.numParams
    val.ctors.anyM fun ctor => do
      forallTelescope (← inferType (mkAppN (.const ctor us) params)) fun fields result => do
        let vars := result.getAppArgs.extract val.numParams
        unless vars.all fields.contains && vars.toList.eraseDups.length == indices.size do
          return false
        fields.allM fun field => do
          if vars.contains field then return true
          let hyp := (← inferType field).replaceFVars vars indices
          isProp hyp <&&> isAlwaysTrue atoms hyp fuel
  | some (.defnInfo _) =>
    let some prop ← unfoldDefinition? prop | return false
    isAlwaysTrue atoms prop fuel
  | _ => return false

/-- A definition of a proposition or a predicate that does not depend on its arguments. -/
structure ConstantPredicate where
  /-- The number of arguments. -/
  arity : Nat
  /-- Whether it is always true. -/
  isAlwaysTrue : Bool
  /-- A description of its values. -/
  msg : MessageData

/--
If `value` is `fun x₁ … xₙ => p` where `p` is a proposition that is always true (see
`isAlwaysTrue`), or that mentions none of `x₁ … xₙ` (with `n > 0`), returns what is known about it.
-/
def constantPredicate? (value : Expr) : MetaM (Option ConstantPredicate) :=
  lambdaTelescope value fun xs body => do
    unless ← isProp body do return none
    if ← isAlwaysTrue #[] body then
      return some { arity := xs.size, isAlwaysTrue := true, msg := "is always true" }
    -- This sees through a `match` whose only pattern is a variable.
    let body ← whnfCore body
    if xs.isEmpty || body.hasAnyFVar fun x => xs.contains (.fvar x) then return none
    return some { arity := xs.size, isAlwaysTrue := false, msg := m!"is always `{body}`" }

/-- Unfolds the constant at the head of `e`, if it is a definition. -/
def unfoldHead? (env : Environment) (e : Expr) : Option Expr := do
  let .const c us := e.getAppFn | none
  let .defnInfo info ← env.find? c | none
  return (info.value.instantiateLevelParams info.levelParams us).beta e.getAppArgs

/-- If `type` is `∀ x₁ … xₙ, Prop`, up to unfolding at most `fuel` definitions, returns `n`. -/
def predicateArity? (env : Environment) (type : Expr) (fuel := 16) : Option Nat :=
  match type with
  | .mdata _ type => predicateArity? env type fuel
  | .forallE _ _ body _ => (· + 1) <$> predicateArity? env body fuel
  | .sort u => if u.isZero then some 0 else none
  | type => match fuel, unfoldHead? env type with
    | fuel + 1, some type => predicateArity? env type fuel
    | _, _ => none

/-- A parameter that is a proposition or a predicate: the name of the constant, and the index of the
parameter. -/
abbrev Slot := Name × Nat

/-- The indices of the parameters of the constant `name` that are propositions or predicates, and
their arities. The motives of recursors do not count. -/
def slotsOf (env : Environment) (name : Name) : Array (Nat × Nat) :=
  match env.find? name with
  | none | some (.recInfo _) => #[]
  | some info =>
    if isAuxRecursor env name || isNoConfusion env name || name matches .str _ "below" then #[]
    else go info.type 0 #[] 16
where
  /-- Adds the parameters in `type`, the first of which has index `i`. -/
  go (type : Expr) (i : Nat) (slots : Array (Nat × Nat)) (fuel : Nat) : Array (Nat × Nat) :=
    match type with
    | .mdata _ type => go type i slots fuel
    | .forallE _ d b _ =>
      let slots := match predicateArity? env d with
        | some n => slots.push (i, n)
        | none => slots
      go b (i + 1) slots fuel
    | type => match fuel, unfoldHead? env type with
      | fuel + 1, some type => go type i slots fuel
      | _, _ => slots

/-- How a variable around an argument is bound. -/
inductive BinderKind
  /-- As the parameter of the declaration with this index. -/
  | param (i : Nat)
  /-- By a `∀` inside of the declaration. -/
  | all
  /-- In some other way, so that its values are not known. -/
  | unknown

/-- An argument for a predicate parameter. -/
structure Arg where
  /-- The declaration that contains the argument. -/
  owner : Name
  /-- The types and kinds of the variables that are bound around the argument, innermost first. -/
  ctx : List (Expr × BinderKind)
  /-- The argument, unless the constant is applied to too few arguments. -/
  value? : Option Expr

/-- The state of `argsOf`. -/
structure ArgsState where
  /-- The terms that were visited, and the binder that they are under. -/
  seen : Std.HashSet (Expr × Nat) := {}
  /-- The number of binders that were visited. -/
  numBinders : Nat := 0
  /-- The arguments. -/
  args : Array (Slot × Arg) := #[]

/-- The arguments for predicate parameters in the declaration `info`, where `slots` are the indices
of the parameters of each constant. -/
partial def argsOf (slots : Name → Array Nat) (info : ConstantInfo) : Array (Slot × Arg) :=
  (go' |>.run {}).2.args
where
  /-- Visits the type and the value. -/
  go' : StateM ArgsState Unit := do
    go info.type [] 0 (some 0) (inType := true)
    if let some value := info.value? (allowOpaque := true) then
      go value [] 0 (some 0) (inType := false)
  /-- Records that `c` is applied to `args`. -/
  record (c : Name) (args : Array Expr) (ctx : List (Expr × BinderKind)) : StateM ArgsState Unit :=
    for i in slots c do
      modify fun s => { s with
        args := s.args.push ((c, i), { owner := info.name, ctx, value? := args[i]? }) }
  /-- Visits `e`, which is under the binder number `id`. If `param?` is an index, then the next
  binder is the parameter of the declaration with this index. -/
  go (e : Expr) (ctx : List (Expr × BinderKind)) (id : Nat) (param? : Option Nat) (inType : Bool) :
      StateM ArgsState Unit := do
    let (ctx, id) := if e.hasLooseBVars then (ctx, id) else ([], 0)
    if (← get).seen.contains (e, id) then return
    modify fun s => { s with seen := s.seen.insert (e, id) }
    let under (d b : Expr) (isParam : Bool) (kind : BinderKind) : StateM ArgsState Unit := do
      go d ctx id none inType
      let id ← modifyGet fun s => (s.numBinders + 1, { s with numBinders := s.numBinders + 1 })
      match param? with
      | some i =>
        if isParam then go b ((d, .param i) :: ctx) id (some (i + 1)) inType
        else go b ((d, kind) :: ctx) id none inType
      | none => go b ((d, kind) :: ctx) id none inType
    match e with
    | .lam _ d b _ => under d b (isParam := !inType) .unknown
    | .forallE _ d b _ => under d b (isParam := inType) .all
    | .letE _ t v b _ => go v ctx id none inType; under t b (isParam := false) .unknown
    | .mdata _ b => go b ctx id param? inType
    | .proj _ _ b => go b ctx id none inType
    | .const c _ => record c #[] ctx
    | .app .. =>
      let f := e.getAppFn
      let args := e.getAppArgs
      if let .const c _ := f then record c args ctx else go f ctx id none inType
      for arg in args do go arg ctx id none inType
    | _ => return

/-- The reachable predicates in scope, and where they are used. -/
structure Flow where
  /-- The roots. -/
  roots : Array Name
  /-- The constants that the statements of the roots refer to, directly or indirectly. -/
  stated : Std.HashSet Name
  /-- The parameters of each constant that are propositions or predicates, and their arities. -/
  slots : Std.HashMap Name (Array (Nat × Nat))
  /-- The declarations that refer to a constant. -/
  users : Std.HashMap Name (Array Name)

/-- What is known about an argument for a predicate parameter. -/
structure CheckedArg where
  /-- The parameter. -/
  slot : Slot
  /-- The argument, unless the constant is applied to too few arguments. -/
  value? : Option Expr
  /-- If the argument is always true whenever the predicates that it is built from are, the
  parameters that these come from. Otherwise, a description of the argument. -/
  sources : Except MessageData (Array Slot)

/-- A monad that remembers the arguments in each declaration. -/
abbrev FlowM := StateRefT (Std.HashMap Name (Array CheckedArg)) MetaM

namespace Flow

/-- Adds the subterms of `e` to `es`. -/
partial def addSubterms (es : Std.HashSet Expr) (e : Expr) : Std.HashSet Expr :=
  if es.contains e then es else e.foldlM (m := Id) addSubterms (es.insert e)

/-- The predicates in `value` whose values are not given by `value` itself, and the parameters that
they come from. These are variables, of which `xs` are the kinds, and structure fields. The
parameter is `none` if the predicate is unknown. -/
def sources (flow : Flow) (owner : Name) (value : Expr) (xs : Array (Expr × BinderKind)) :
    MetaM (Array (Expr × Option Slot)) := do
  let env ← getEnv
  let mut sources := #[]
  for (x, kind) in xs do
    if value.containsFVar x.fvarId! && (predicateArity? env (← inferType x)).isSome then
      match kind with
      | .param i => sources := sources.push (x, some (owner, i))
      | .unknown => sources := sources.push (x, none)
      -- The analysis follows actual values, and a quantifier ranges over all of them.
      | .all => pure ()
  let isField (e : Expr) : Option (Name × Nat) := match e with
    | .proj s i _ => do
      let .inductInfo { ctors := [ctor], numParams, .. } ← env.find? s | none
      return (ctor, numParams + i)
    | .app .. => do
      let info ← env.getProjectionFnInfo? (← e.getAppFn.constName?)
      -- A field of a class is unfolded instead, if the instance is known.
      guard (!info.fromClass && e.getAppNumArgs == info.numParams + 1)
      return (info.ctorName, info.numParams + info.i)
    | _ => none
  for e in addSubterms {} value do
    let some (ctor, i) := isField e | continue
    if !e.hasLooseBVars && (predicateArity? env (← inferType e)).isSome then
      let known := (flow.slots.getD ctor #[]).any (·.1 == i)
      sources := sources.push (e, if known then some (ctor, i) else none)
  return sources

/-- Computes `CheckedArg.sources`. -/
def check (flow : Flow) (arg : Arg) : MetaM (Except MessageData (Array Slot)) := do
  let some value := arg.value? | return .error "a value that is not known"
  go value arg.ctx.reverse #[]
where
  /-- Introduces the variables `ctx`, given the variables `xs` around them. -/
  go (value : Expr) (ctx : List (Expr × BinderKind)) (xs : Array (Expr × BinderKind)) :
      MetaM (Except MessageData (Array Slot)) := do
    if let (type, kind) :: ctx := ctx then
      return ← withLocalDeclD `x (type.instantiateRev (xs.map (·.1))) fun x =>
        go value ctx (xs.push (x, kind))
    let value := (value.instantiateRev (xs.map (·.1))).consumeMData.eta
    let sources ← flow.sources arg.owner value xs
    let atoms := sources.map (·.1) ++ xs.filterMap fun (x, kind) =>
      if kind matches .all then some x else none
    let ok ← forallTelescopeReducing (← inferType value) fun ys _ =>
      isAlwaysTrue atoms (value.beta ys)
    unless ok do
      return .error <| match value.getAppFn with
        | .const c _ => m!"`{.ofConstName c}`"
        | _ => "another value"
    if sources.any (·.2.isNone) then return .error "a value that is not known"
    return .ok (sources.filterMap (·.2))

/-- The arguments for predicate parameters in the declaration `name`. -/
def argsIn (flow : Flow) (name : Name) : FlowM (Array CheckedArg) := do
  if let some args := (← get)[name]? then return args
  let args := argsOf (fun c => (flow.slots.getD c #[]).map (·.1)) (← getConstInfo name)
  let args ← args.mapM fun (slot, arg) => do
    let sources ← guarded (.error "a value that is not known") (flow.check arg)
    return { slot, value? := arg.value?, sources : CheckedArg }
  modify (·.insert name args)
  return args

/-- The declarations in which the predicates that reach `slot` are available: the one that `slot` is
a parameter of, and if `slot` is a structure field, the ones that read it. -/
def readers (flow : Flow) (slot : Slot) : MetaM (Array Name) := do
  let some (.ctorInfo { induct, numParams, .. }) := (← getEnv).find? slot.1 | return #[slot.1]
  if slot.2 < numParams then return #[slot.1]
  let projFn? := getStructureInfo? (← getEnv) induct |>.bind (·.getProjFn? (slot.2 - numParams))
  return #[slot.1] ++ flow.users.getD induct #[] ++
    (projFn?.map (flow.users.getD · #[])).getD #[]

/--
Looks for an alternative to `name`, which is a proposition or a predicate of the given arity that is
always true: a value that is not always true, but reaches a parameter that `name` reaches. If there
is none, returns the constants that take `name` as an argument. Otherwise, returns a description of
the alternative.

If `name` is a predicate, then the parameters that are propositions do not count. They are where a
value of the predicate goes, and they are often parameters of general lemmas.
-/
def alternative? (flow : Flow) (name : Name) (arity : Nat) :
    FlowM (Except MessageData (Array Name)) := do
  if flow.stated.contains name then return .error "it is part of what the roots state"
  let counts (slot : Slot) : Bool := arity == 0 ||
    (flow.slots.getD slot.1 #[]).any fun (i, n) => i == slot.2 && n > 0
  let mut direct := #[]
  for owner in flow.users.getD name #[] do
    for arg in ← flow.argsIn owner do
      if arg.sources matches .ok _ && counts arg.slot then
        if arg.value?.any (·.getUsedConstants.contains name) then direct := direct.push arg.slot
  -- A proposition can be used without being an argument, for example as a hypothesis.
  if direct.isEmpty && arity > 0 then
    return .error "it is never an argument for a predicate parameter in scope"
  -- The parameters that `name` reaches, and the ones that these get their values from. Following
  -- `name` can lead through every declaration that reads a structure field, so look for an
  -- alternative at each parameter before going on.
  let mut reached : Std.HashSet Slot := {}
  let mut seen : Std.HashSet Slot := {}
  let mut forward := direct
  let mut backward := direct
  repeat
    if let some slot := backward.back? then
      backward := backward.pop
      if seen.contains slot then continue
      seen := seen.insert slot
      if flow.roots.contains slot.1 then
        return .error m!"the root `{.ofConstName slot.1}` has a predicate as a parameter"
      for owner in flow.users.getD slot.1 #[] do
        for arg in ← flow.argsIn owner do
          if arg.slot == slot then
            match arg.sources with
            | .ok slots => backward := backward ++ slots
            | .error value => return .error m!"`{.ofConstName slot.1}` also gets {value}"
    else
      let some slot := forward.back? | break
      forward := forward.pop
      if reached.contains slot then continue
      reached := reached.insert slot
      let mut next := #[]
      for owner in ← flow.readers slot do
        for arg in ← flow.argsIn owner do
          if let .ok slots := arg.sources then
            if slots.contains slot && counts arg.slot then next := next.push arg.slot
      -- A value of an inductive type contains the fields of a constructor with the same parameters.
      if let some (.inductInfo { numParams, ctors, .. }) := (← getEnv).find? slot.1 then
        if slot.2 < numParams then next := next ++ (ctors.map (·, slot.2)).toArray
      forward := forward ++ next
      backward := backward ++ next
  return .ok <| (Std.HashSet.ofArray (direct.map (·.1))).toArray.qsort Name.lt

end Flow

/-- Collects the predicates among the constants `consts` in scope. The constant predicates are
`preds`. -/
def mkFlow (env : Environment) (roots : Array Name) (consts : Std.HashSet Name)
    (inScope : Name → Bool) (preds : Array Name) : Flow := Id.run do
  let statements := roots.foldl (init := ({} : Uses)) fun uses root =>
    match env.find? root with
    | some info => uses.addExpr info.type
    | none => uses
  let stated := (reach env statements.consts.toArray).consts
  let consts := consts.toArray.filter inScope
  let mut slots := {}
  -- The constants to find the users of.
  let mut used : Std.HashSet Name := .ofArray preds
  for c in consts do
    let cs := slotsOf env c
    unless cs.isEmpty do
      slots := slots.insert c cs
      used := used.insert c
      if let some (.ctorInfo { induct, numParams, .. }) := env.find? c then
        used := used.insert induct
        if let some info := getStructureInfo? env induct then
          for (i, _) in cs do
            if let some projFn := info.getProjFn? (i - numParams) then
              if i ≥ numParams then used := used.insert projFn
  let mut users := {}
  for owner in consts do
    let some info := env.find? owner | continue
    for c in (Uses.addConstantInfo {} info).consts do
      if used.contains c then
        users := users.alter c fun owners? => some ((owners?.getD #[]).push owner)
  return { roots, stated, slots, users }

/-- Whether `value` is `fun x₁ … xₙ => b` with `n > 0`, where `b` mentions none of `x₁ … xₙ`. -/
def isConstantFunction : Expr → Bool
  | .mdata _ e => isConstantFunction e
  | .lam _ _ b _ => go b
  | _ => false
where
  /-- Whether the body of the remaining lambdas is closed. -/
  go : Expr → Bool
    | .mdata _ e => go e
    | .lam _ _ b _ => go b
    | e => !e.hasLooseBVars

/--
Finds the dead weight among the declarations that satisfy `inScope`: the parts that the constants
`roots` do not use.
-/
def analyze (roots : Array Name) (inScope : Name → Bool) : MetaM Report := do
  let env ← getEnv
  for root in roots do
    unless env.contains root do throwError "unknown constant '{root}'"
  let { consts, projs } := reach env roots
  let mut report : Report := { numReached := consts.size }
  let mut constantPredicates := #[]
  let mut dead : Std.HashMap Name (Array Name) := {}
  let mut liveModules : Std.HashSet Name := {}
  for (name, info) in env.constants do
    if info matches .axiomInfo _ && consts.contains name then
      report := { report with axioms := report.axioms.push name }
    unless inScope name do continue
    let mod := match env.getModuleIdxFor? name with
      | some idx => env.header.moduleNames[idx]!
      | none => env.mainModule
    let reached := consts.contains name
    if reached then liveModules := liveModules.insert mod
    if env.isAutoDecl name then continue
    -- Constructors, recursors and projections belong to their inductive type.
    if env.isProjectionFn name || info matches .ctorInfo _ | .recInfo _ then continue
    report := { report with numDecls := report.numDecls + 1 }
    unless reached do
      report := { report with numDead := report.numDead + 1 }
      dead := dead.insert mod ((dead.getD mod #[]).push name)
      continue
    if let some { fieldNames, .. } := getStructureInfo? env name then
      let destructured := consts.contains (mkRecName name)
      for fieldName in fieldNames, i in [0:fieldNames.size] do
        let projFn? := getProjFnForField? env name fieldName
        unless projs.contains (name, i) || projFn?.any consts.contains do
          let field := { structName := name, fieldName, destructured }
          report := { report with unreadFields := report.unreadFields.push field }
    if let .defnInfo { value, type, .. } := info then
      if let some pred ← guarded none (constantPredicate? value) then
        constantPredicates := constantPredicates.push (name, pred)
      else if isConstantFunction value && !(← guarded true (isProp type)) &&
          !(← isInstance name) then
        report := { report with constantFunctions := report.constantFunctions.push name }
  let vacuous := constantPredicates.filterMap fun (name, pred) =>
    if pred.isAlwaysTrue then some name else none
  let flow := if vacuous.isEmpty then { roots, stated := {}, slots := {}, users := {} } else
    mkFlow env roots consts inScope vacuous
  let mut cache := {}
  for (name, pred) in constantPredicates do
    let mut msg := pred.msg
    if pred.isAlwaysTrue then
      let (result, cache') ← (flow.alternative? name pred.arity).run cache
      cache := cache'
      match result with
      | .ok filled =>
        report := { report with vacuousPredicates := report.vacuousPredicates.push (name, filled) }
        continue
      | .error why => msg := m!"{msg}, but {why}"
    msg ← addMessageContext msg
    report := { report with constantPredicates := report.constantPredicates.push (name, msg) }
  let deadModules := dead.keysArray.filter (!liveModules.contains ·)
  let deadDecls := dead.toArray.flatMap fun (mod, decls) =>
    if liveModules.contains mod then decls else #[]
  return { report with
    deadModules := deadModules.qsort Name.lt
    deadDecls := deadDecls.qsort Name.lt
    unreadFields := report.unreadFields.qsort fun a b =>
      (a.structName ++ a.fieldName).lt (b.structName ++ b.fieldName)
    vacuousPredicates := report.vacuousPredicates.qsort (·.1.lt ·.1)
    constantPredicates := report.constantPredicates.qsort (·.1.lt ·.1)
    constantFunctions := report.constantFunctions.qsort Name.lt
    axioms := report.axioms.qsort Name.lt }

end Batteries.DeadWeight
