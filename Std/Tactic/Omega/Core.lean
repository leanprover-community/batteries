/-
Copyright (c) 2023 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Std.Tactic.Omega.OmegaM
import Std.Tactic.Omega.Constraint
import Std.Tactic.Omega.MinNatAbs

open Lean (HashMap HashSet)

namespace Std.Tactic.Omega

open Lean (Expr)
open Lean.Meta

/--
A delayed proof that a constraint is satisfied at the atoms.
-/
abbrev Proof : Type := OmegaM Expr

/--
Normalize a constraint, by dividing through by the GCD.

Return `none` if there is nothing to do, to avoid adding unnecessary steps to the proof term.
-/
def normalize? : Constraint × Coeffs → Option (Constraint × Coeffs)
  | ⟨s, x⟩ =>
    let gcd := Coeffs.gcd x -- TODO should we be caching this?
    if gcd = 0 then
      if s.sat 0 then
        some (.trivial, x)
      else
        some (.impossible, x)
    else if gcd = 1 then
      none
    else
      some (s.div gcd, Coeffs.sdiv x gcd)

/-- Normalize a constraint, by dividing through by the GCD. -/
def normalize (p : Constraint × Coeffs) : Constraint × Coeffs :=
  normalize? p |>.getD p

/-- Shorthand for the first component of `normalize`. -/
-- This `noncomputable` (and others below) is a safeguard that we only use this in proofs.
noncomputable abbrev normalizeConstraint (s : Constraint) (x : Coeffs) : Constraint :=
  (normalize (s, x)).1
/-- Shorthand for the second component of `normalize`. -/
noncomputable abbrev normalizeCoeffs (s : Constraint) (x : Coeffs) : Coeffs :=
  (normalize (s, x)).2

theorem normalize?_eq_some (w : normalize? (s, x) = some (s', x')) :
    normalizeConstraint s x = s' ∧ normalizeCoeffs s x = x' := by
  simp_all [normalizeConstraint, normalizeCoeffs, normalize]

theorem normalize_sat {s x v} (w : s.sat' x v) :
    (normalizeConstraint s x).sat' (normalizeCoeffs s x) v := by
  dsimp [normalizeConstraint, normalizeCoeffs, normalize, normalize?]
  split <;> rename_i h
  · split
    · simp
    · dsimp [Constraint.sat'] at w
      simp_all
  · split
    · exact w
    · exact Constraint.div_sat' h w

/-- Multiply by `-1` if the leading coefficient is negative, otherwise return `none`. -/
def positivize? : Constraint × Coeffs → Option (Constraint × Coeffs)
  | ⟨s, x⟩ =>
    if 0 ≤ x.leading then
      none
    else
      (s.neg, Coeffs.smul x (-1))

/-- Multiply by `-1` if the leading coefficient is negative, otherwise do nothing. -/
noncomputable def positivize (p : Constraint × Coeffs) : Constraint × Coeffs :=
  positivize? p |>.getD p

/-- Shorthand for the first component of `positivize`. -/
noncomputable abbrev positivizeConstraint (s : Constraint) (x : Coeffs) : Constraint :=
  (positivize (s, x)).1
/-- Shorthand for the second component of `positivize`. -/
noncomputable abbrev positivizeCoeffs (s : Constraint) (x : Coeffs) : Coeffs :=
  (positivize (s, x)).2

theorem positivize?_eq_some (w : positivize? (s, x) = some (s', x')) :
    positivizeConstraint s x = s' ∧ positivizeCoeffs s x = x' := by
  simp_all [positivizeConstraint, positivizeCoeffs, positivize]

theorem positivize_sat {s x v} (w : s.sat' x v) :
    (positivizeConstraint s x).sat' (positivizeCoeffs s x) v := by
  dsimp [positivizeConstraint, positivizeCoeffs, positivize, positivize?]
  split
  · exact w
  · simp [Constraint.sat']
    erw [Coeffs.dot_smul_left, ← Int.neg_eq_neg_one_mul]
    exact Constraint.neg_sat w

/-- `positivize` and `normalize`, returning `none` if neither does anything. -/
def tidy? : Constraint × Coeffs → Option (Constraint × Coeffs)
  | ⟨s, x⟩ =>
    match positivize? (s, x) with
    | none => match normalize? (s, x) with
      | none => none
      | some (s', x') => some (s', x')
    | some (s', x') => normalize (s', x')

/-- `positivize` and `normalize` -/
def tidy (p : Constraint × Coeffs) : Constraint × Coeffs :=
  tidy? p |>.getD p

/-- Shorthand for the first component of `tidy`. -/
abbrev tidyConstraint (s : Constraint) (x : Coeffs) : Constraint := (tidy (s, x)).1
/-- Shorthand for the second component of `tidy`. -/
abbrev tidyCoeffs (s : Constraint) (x : Coeffs) : Coeffs := (tidy (s, x)).2

theorem tidy_sat {s x v} (w : s.sat' x v) : (tidyConstraint s x).sat' (tidyCoeffs s x) v := by
  dsimp [tidyConstraint, tidyCoeffs, tidy, tidy?]
  split <;> rename_i hp
  · split <;> rename_i hn
    · simp_all
    · rcases normalize?_eq_some hn with ⟨rfl, rfl⟩
      exact normalize_sat w
  · rcases positivize?_eq_some hp with ⟨rfl, rfl⟩
    exact normalize_sat (positivize_sat w)

theorem combo_sat' (s t : Constraint)
    (a : Int) (x : Coeffs) (b : Int) (y : Coeffs) (v : Coeffs)
    (wx : s.sat' x v) (wy : t.sat' y v) :
    (Constraint.combo a s b t).sat' (Coeffs.combo a x b y) v := by
  rw [Constraint.sat', Coeffs.combo_eq_smul_add_smul, Coeffs.dot_distrib_left,
    Coeffs.dot_smul_left, Coeffs.dot_smul_left]
  exact Constraint.combo_sat a wx b wy

/-- The value of the new variable introduced when solving a hard equality. -/
abbrev bmod_div_term (m : Nat) (a b : Coeffs) : Int := Coeffs.bmod_dot_sub_dot_bmod m a b / m

/-- The coefficients of the new equation generated when solving a hard equality. -/
def bmod_coeffs (m : Nat) (i : Nat) (x : Coeffs) : Coeffs :=
  Coeffs.set (Coeffs.bmod x m) i m

theorem bmod_sat (m : Nat) (r : Int) (i : Nat) (x v : Coeffs)
    (h : x.length ≤ i)  -- during proof reconstruction this will be by `decide`
    (p : Coeffs.get v i = bmod_div_term m x v) -- and this will be by `rfl`
    (w : (Constraint.exact r).sat' x v) :
    (Constraint.exact (Int.bmod r m)).sat' (bmod_coeffs m i x) v := by
  simp at w
  simp only [p, bmod_coeffs, Constraint.exact_sat, Coeffs.dot_set_left, decide_eq_true_eq]
  replace h := Nat.le_trans (Coeffs.bmod_length x m) h
  rw [Coeffs.get_of_length_le h, Int.sub_zero,
    Int.mul_ediv_cancel' (Coeffs.dvd_bmod_dot_sub_dot_bmod _ _ _), w,
    ← Int.add_sub_assoc, Int.add_comm, Int.add_sub_assoc, Int.sub_self, Int.add_zero]

/--
Our internal representation of argument "justifying" that a constraint holds on some coefficients.
We'll use this to construct the proof term once a contradiction is found.
-/
inductive Justification : Constraint → Coeffs → Type
  /--
  `Problem.assumptions[i]` generates a proof that `s.sat' coeffs atoms`
  -/
  | assumption (s : Constraint) (x : Coeffs) (i : Nat) : Justification s x
  /-- The result of `tidy` on another `Justification`. -/
  | tidy (j : Justification s c) : Justification (tidyConstraint s c) (tidyCoeffs s c)
  /-- The result of `combine` on two `Justifications`. -/
  | combine {s t c} (j : Justification s c) (k : Justification t c) : Justification (s.combine t) c
  /-- A linear `combo` of two `Justifications`. -/
  | combo {s t x y} (a : Int) (j : Justification s x) (b : Int) (k : Justification t y) :
    Justification (Constraint.combo a s b t) (Coeffs.combo a x b y)
  /--
  The justification for the constraing constructed using "balanced mod" while
  eliminating an equality.
  -/
  | bmod (m : Nat) (r : Int) (i : Nat) {x} (j : Justification (.exact r) x) :
      Justification (.exact (Int.bmod r m)) (bmod_coeffs m i x)

/-- Wrapping for `Justification.tidy` when `tidy?` is nonempty. -/
nonrec def Justification.tidy? (j : Justification s c) : Option (Σ s' c', Justification s' c') :=
  match tidy? (s, c) with
  | some _ => some ⟨_, _, tidy j⟩
  | none => none

namespace Justification

private def bullet (s : String) := "• " ++ s.replace "\n" "\n  "

/-- Print a `Justification` as an indented tree structure. -/
def toString : Justification s x → String
  | assumption _ _ i => s!"{x} ∈ {s}: assumption {i}"
  | @tidy s' x' j =>
    if s == s' && x == x' then j.toString else s!"{x} ∈ {s}: tidying up:\n" ++ bullet j.toString
  | combine j k =>
    s!"{x} ∈ {s}: combination of:\n" ++ bullet j.toString ++ "\n" ++ bullet k.toString
  | combo a j b k =>
    s!"{x} ∈ {s}: {a} * x + {b} * y combo of:\n" ++ bullet j.toString ++ "\n" ++ bullet k.toString
  | bmod m _ i j =>
    s!"{x} ∈ {s}: bmod with m={m} and i={i} of:\n" ++ bullet j.toString

instance : ToString (Justification s x) where toString := toString

open Lean

/-- Construct the proof term associated to a `tidy` step. -/
def tidyProof (s : Constraint) (x : Coeffs) (v : Expr) (prf : Expr) : Expr :=
  mkApp4 (.const ``tidy_sat []) (toExpr s) (toExpr x) v prf

/-- Construct the proof term associated to a `combine` step. -/
def combineProof (s t : Constraint) (x : Coeffs) (v : Expr) (ps pt : Expr) : Expr :=
  mkApp6 (.const ``Constraint.combine_sat' []) (toExpr s) (toExpr t) (toExpr x) v ps pt

/-- Construct the proof term associated to a `combo` step. -/
def comboProof (s t : Constraint) (a : Int) (x : Coeffs) (b : Int) (y : Coeffs)
    (v : Expr) (px py : Expr) : Expr :=
  mkApp9 (.const ``combo_sat' []) (toExpr s) (toExpr t) (toExpr a) (toExpr x) (toExpr b) (toExpr y)
    v px py

/-- Construct the proof term associated to a `bmod` step. -/
def bmodProof (m : Nat) (r : Int) (i : Nat) (x : Coeffs) (v : Expr) (w : Expr) : MetaM Expr := do
  let m := toExpr m
  let r := toExpr r
  let i := toExpr i
  let x := toExpr x
  let h ← mkDecideProof (mkApp4 (.const ``LE.le [.zero]) (.const ``Nat []) (.const ``instLENat [])
    (.app (.const ``Coeffs.length []) x) i)
  let lhs := mkApp2 (.const ``Coeffs.get []) v i
  let rhs := mkApp3 (.const ``bmod_div_term []) m x v
  let p ← mkEqReflWithExpectedType lhs rhs
  return mkApp8 (.const ``bmod_sat []) m r i x v h p w

-- TODO could we increase sharing in the proof term here?

/-- Constructs a proof that `s.sat' c v = true` -/
def proof (v : Expr) (assumptions : Array Proof) : Justification s c → Proof
  | assumption s c i => assumptions[i]!
  | @tidy s c j => return tidyProof s c v (← proof v assumptions j)
  | @combine s t c j k =>
    return combineProof s t c v (← proof v assumptions j) (← proof v assumptions k)
  | @combo s t x y a j b k =>
    return comboProof s t a x b y v (← proof v assumptions j) (← proof v assumptions k)
  | @bmod m r i x j => do bmodProof m r i x v (← proof v assumptions j)

end Justification

/-- A `Justification` bundled together with its parameters. -/
structure Fact where
  /-- The coefficients of a constraint. -/
  coeffs : Coeffs
  /-- The constraint. -/
  constraint : Constraint
  /-- The justification of a derived fact. -/
  justification : Justification constraint coeffs

namespace Fact

instance : ToString Fact where
  toString f := toString f.justification

/-- `tidy`, implemented on `Fact`. -/
def tidy (f : Fact) : Fact :=
  match f.justification.tidy? with
  | some ⟨_, _, justification⟩ => { justification }
  | none => f

/-- `combo`, implemented on `Fact`. -/
def combo (a : Int) (f : Fact) (b : Int) (g : Fact) : Fact :=
  { justification := .combo a f.justification b g.justification }

end Fact

/--
A `omega` problem.

This is a hybrid structure:
it contains both `Expr` objects giving proofs of the "ground" assumptions
(or rather continuations which will produce the proofs when needed)
and internal representations of the linear constraints that we manipulate in the algorithm.

While the algorithm is running we do not synthesize any new `Expr` proofs: proof extraction happens
only once we've found a contradiction.
-/
structure Problem where
  /-- The ground assumptions that the algorithm starts from. -/
  assumptions : Array Proof := ∅
  /-- The number of variables in the problem. -/
  numVars : Nat := 0
  /-- The current constraints, indexed by their coefficients. -/
  constraints : HashMap Coeffs Fact := ∅
  /--
  The coefficients for which `constraints` contains an exact constraint (i.e. an equality).
  -/
  equalities : HashSet Coeffs := ∅
  /--
  Equations that have already been used to eliminate variables,
  along with the variable which was removed, and its coefficient (either `1` or `-1`).
  The earlier elements are more recent,
  so if these are being reapplied it is essential to use `List.foldr`.
  -/
  eliminations : List (Fact × Nat × Int) := []
  /-- Whether the problem is possible. -/
  possible : Bool := true
  /-- If the problem is impossible, then `proveFalse?` will contain a proof of `False`. -/
  proveFalse? : Option Proof := none
  /-- Invariant between `possible` and `proveFalse?`. -/
  proveFalse?_spec : possible || proveFalse?.isSome := by rfl
  /--
  If we have found a contradiction,
  `explanation?` will contain a human readable account of the deriviation.
  -/
  explanation? : Thunk String := ""

namespace Problem

/-- Check if a problem has no constraints. -/
def isEmpty (p : Problem) : Bool := p.constraints.isEmpty

instance : ToString Problem where
  toString p :=
    if p.possible then
      if p.isEmpty then
        "trivial"
      else
        "\n".intercalate <|
          (p.constraints.toList.map fun ⟨coeffs, ⟨_, cst, _⟩⟩ => s!"{coeffs} ∈ {cst}")
    else
      "impossible"

open Lean in
/--
Takes a proof that `s.sat' x v` for some `s` such that `s.isImpossible`,
and constructs a proof of `False`.
-/
def proveFalse {s x} (j : Justification s x) (assumptions : Array Proof) : Proof := do
  let v := ← atomsCoeffs
  let prf ← j.proof v assumptions
  let x := toExpr x
  let s := toExpr s
  let impossible ←
    mkDecideProof (← mkEq (mkApp (.const ``Constraint.isImpossible []) s) (.const ``true []))
  return mkApp5 (.const ``Constraint.not_sat'_of_isImpossible []) s impossible x v prf

/--
Insert a constraint into the problem,
without checking if there is already a constraint for these coefficients.
-/
def insertConstraint (p : Problem) : Fact → Problem
  | f@⟨x, s, j⟩ =>
    if s.isImpossible then
      { p with
        possible := false
        proveFalse? := some (proveFalse j p.assumptions)
        explanation? := Thunk.mk fun _ => j.toString
        proveFalse?_spec := rfl }
    else
      { p with
        numVars := max p.numVars x.length
        constraints := p.constraints.insert x f
        proveFalse?_spec := p.proveFalse?_spec
        equalities :=
        if f.constraint.isExact then
          p.equalities.insert x
        else
          p.equalities }

/--
Add a constraint into the problem,
combining it with any existing constraints for the same coefficients.
-/
def addConstraint (p : Problem) : Fact → Problem
  | f@⟨x, s, j⟩ =>
    if p.possible then
      match p.constraints.find? x with
      | none =>
        match s with
        | .trivial => p
        | _ => p.insertConstraint f
      | some ⟨x', t, k⟩ =>
        if h : x = x' then
          let r := s.combine t
          if r = t then
            -- No need to overwrite the existing fact
            -- with the same fact with a more complicated justification
            p
          else
            if r = s then
              -- The new constraint is strictly stronger, no need to combine with the old one:
              p.insertConstraint ⟨x, s, j⟩
            else
              p.insertConstraint ⟨x, s.combine t, j.combine (h ▸ k)⟩
        else
          p -- unreachable
    else
      p

/--
Walk through the equalities, finding either the first equality with minimal coefficient `±1`,
or otherwise the equality with minimal `(r.minNatAbs, r.maxNatAbs)` (ordered lexicographically).

Returns the coefficients of the equality, along with the value of `minNatAbs`.

Although we don't need to run a termination proof here, it's nevertheless important that we use this
ordering so the algorithm terminates in practice!
-/
def selectEquality (p : Problem) : Option (Coeffs × Nat) :=
  p.equalities.fold (init := none) fun
  | none, c => (c, c.minNatAbs)
  | some (r, m), c =>
    if 2 ≤ m then
      let m' := c.minNatAbs
      if (m' < m || m' = m && c.maxNatAbs < r.maxNatAbs) then
        (c, m')
      else
        (r, m)
    else
      (r, m)

/--
If we have already solved some equalities, apply those to some new `Fact`.
-/
def replayEliminations (p : Problem) (f : Fact) : Fact :=
  p.eliminations.foldr (init := f) fun (f, i, s) g =>
    match Coeffs.get g.coeffs i with
    | 0 => g
    | y => Fact.combo (-1 * s * y) f 1 g

/--
Solve an "easy" equality, i.e. one with a coefficient that is `±1`.

After solving, the variable will have been eliminated from all constraints.
-/
def solveEasyEquality (p : Problem) (c : Coeffs) : Problem :=
  let i := c.findIdx? (·.natAbs = 1) |>.getD 0 -- findIdx? is always some
  let sign := c.get i |> Int.sign
  match p.constraints.find? c with
  | some f =>
    let init :=
    { assumptions := p.assumptions
      eliminations := (f, i, sign) :: p.eliminations }
    p.constraints.fold (init := init) fun p' coeffs g =>
      match Coeffs.get coeffs i with
      | 0 =>
        p'.addConstraint g
      | ci =>
        let k := -1 * sign * ci
        p'.addConstraint (Fact.combo k f 1 g).tidy
  | _ => p -- unreachable

open Lean in
/--
We deal with a hard equality by introducing a new easy equality.

After solving the easy equality,
the minimum lexicographic value of `(c.minNatAbs, c.maxNatAbs)` will have been reduced.
-/
def dealWithHardEquality (p : Problem) (c : Coeffs) : OmegaM Problem :=
  match p.constraints.find? c with
  | some ⟨_, ⟨some r, some r'⟩, j⟩ => do
    let m := c.minNatAbs + 1
    -- We have to store the valid value of the newly introduced variable in the atoms.
    let x := mkApp3 (.const ``bmod_div_term []) (toExpr m) (toExpr c) (← atomsCoeffs)
    let (i, facts?) ← lookup x
    if hr : r' = r then
      match facts? with
      | none => throwError "When solving hard equality, new atom had been seen before!"
      | some facts => if ! facts.isEmpty then
        throwError "When solving hard equality, there were unexpected new facts!"
      return p.addConstraint { coeffs := _, constraint := _, justification := (hr ▸ j).bmod m r i }
    else
      throwError "Invalid constraint, expected an equation." -- unreachable
  | _ =>
    return p -- unreachable

/--
Solve an equality, by deciding whether it is easy (has a `±1` coefficient) or hard,
and delegating to the appropriate function.
-/
def solveEquality (p : Problem) (c : Coeffs) (m : Nat) : OmegaM Problem :=
  if m = 1 then
    return p.solveEasyEquality c
  else
    p.dealWithHardEquality c

/-- Recursively solve all equalities. -/
partial def solveEqualities (p : Problem) : OmegaM Problem :=
  if p.possible then
    match p.selectEquality with
    | some (c, m) => do (← p.solveEquality c m).solveEqualities
    | none => return p
  else return p

theorem addInequality_sat (w : c + Coeffs.dot x y ≥ 0) :
    Constraint.sat' { lowerBound := some (-c), upperBound := none } x y := by
  simp [Constraint.sat', Constraint.sat]
  rw [← Int.zero_sub c]
  exact Int.sub_left_le_of_le_add w

open Lean in
/-- Constructing the proof term for `addInequality`. -/
def addInequality_proof (c : Int) (x : Coeffs) (p : Proof) : Proof := do
  return mkApp4 (.const ``addInequality_sat []) (toExpr c) (toExpr x) (← atomsCoeffs) (← p)

theorem addEquality_sat (w : c + Coeffs.dot x y = 0) :
    Constraint.sat' { lowerBound := some (-c), upperBound := some (-c) } x y := by
  simp [Constraint.sat', Constraint.sat]
  rw [Int.eq_iff_le_and_ge] at w
  rwa [Int.add_le_zero_iff_le_neg', Int.add_nonnneg_iff_neg_le', and_comm] at w

open Lean in
/-- Constructing the proof term for `addEquality`. -/
def addEquality_proof (c : Int) (x : Coeffs) (p : Proof) : Proof := do
  return mkApp4 (.const ``addEquality_sat []) (toExpr c) (toExpr x) (← atomsCoeffs) (← p)

/--
Helper function for adding an inequality of the form `const + Coeffs.dot coeffs atoms ≥ 0`
to a `Problem`.

(This is only used while initializing a `Problem`. During elimination we use `addConstraint`.)
-/
-- We are given `prf? : const + Coeffs.dot coeffs atoms ≥ 0`,
-- and need to transform this to `Coeffs.dot coeffs atoms ≥ -const`.
def addInequality (p : Problem) (const : Int) (coeffs : Coeffs) (prf? : Option Proof) : Problem :=
  let prf := prf?.getD (do mkSorry (← mkFreshExprMVar none) false)
  let i := p.assumptions.size
  let p' := { p with assumptions := p.assumptions.push (addInequality_proof const coeffs prf) }
  let f : Fact :=
  { coeffs
    constraint := { lowerBound := some (-const), upperBound := none }
    justification := .assumption _ _ i }
  let f := p.replayEliminations f
  let f := f.tidy
  p'.addConstraint f

/--
Helper function for adding an equality of the form `const + Coeffs.dot coeffs atoms = 0`
to a `Problem`.

(This is only used while initializing a `Problem`. During elimination we use `addConstraint`.)
-/
def addEquality (p : Problem) (const : Int) (coeffs : Coeffs) (prf? : Option Proof) : Problem :=
  let prf := prf?.getD (do mkSorry (← mkFreshExprMVar none) false)
  let i := p.assumptions.size
  let p' := { p with assumptions := p.assumptions.push (addEquality_proof const coeffs prf) }
  let f : Fact :=
  { coeffs
    constraint := { lowerBound := some (-const), upperBound := some (-const) }
    justification := .assumption _ _ i }
  let f := p.replayEliminations f
  let f := f.tidy
  p'.addConstraint f

/-- Folding `addInequality` over a list. -/
def addInequalities (p : Problem) (ineqs : List (Int × Coeffs × Option Proof)) : Problem :=
  ineqs.foldl (init := p) fun p ⟨const, coeffs, prf?⟩ => p.addInequality const coeffs prf?

/-- Folding `addEquality` over a list. -/
def addEqualities (p : Problem) (eqs : List (Int × Coeffs × Option Proof)) : Problem :=
  eqs.foldl (init := p) fun p ⟨const, coeffs, prf?⟩ => p.addEquality const coeffs prf?

/-- Representation of the data required to run Fourier-Motzkin elimination on a variable. -/
structure FourierMotzkinData where
  /-- Which variable is being eliminated. -/
  var : Nat
  /-- The "irrelevant" facts which do not involve the target variable. -/
  irrelevant : List Fact := []
  /--
  The facts which give a lower bound on the target variable,
  and the coefficient of the target variable in each.
  -/
  lowerBounds : List (Fact × Int) := []
  /--
  The facts which give an upper bound on the target variable,
  and the coefficient of the target variable in each.
  -/
  upperBounds : List (Fact × Int) := []
  /--
  Whether the elimination would be exact, because all of the lower bound coefficients are `±1`.
  -/
  lowerExact : Bool := true
  /--
  Whether the elimination would be exact, because all of the upper bound coefficients are `±1`.
  -/
  upperExact : Bool := true
deriving Inhabited

instance : ToString FourierMotzkinData where
  toString d :=
    let irrelevant := d.irrelevant.map fun ⟨x, s, _⟩ => s!"{x} ∈ {s}"
    let lowerBounds := d.lowerBounds.map fun ⟨⟨x, s, _⟩, _⟩ => s!"{x} ∈ {s}"
    let upperBounds := d.upperBounds.map fun ⟨⟨x, s, _⟩, _⟩ => s!"{x} ∈ {s}"
    s!"Fourier-Motzkin elimination data for variable {d.var}\n"
      ++ s!"• irrelevant: {irrelevant}\n"
      ++ s!"• lowerBounds: {lowerBounds}\n"
      ++ s!"• upperBounds: {upperBounds}"

/-- Is a Fourier-Motzkin elimination empty (i.e. there are no relevant constraints). -/
def FourierMotzkinData.isEmpty (d : FourierMotzkinData) : Bool :=
  d.lowerBounds.isEmpty && d.upperBounds.isEmpty
/-- The number of new constraints that would be introduced by Fourier-Motzkin elimination. -/
def FourierMotzkinData.size (d : FourierMotzkinData) : Nat :=
  d.lowerBounds.length * d.upperBounds.length
/-- Is the Fourier-Motzkin elimination known to be exact? -/
def FourierMotzkinData.exact (d : FourierMotzkinData) : Bool := d.lowerExact || d.upperExact

/-- Prepare the Fourier-Motzkin elimination data for each variable. -/
-- TODO we could short-circuit here, if we find one with `size = 0`.
def fourierMotzkinData (p : Problem) : Array FourierMotzkinData := Id.run do
  let n := p.numVars
  let mut data : Array FourierMotzkinData :=
    (List.range p.numVars).foldl (fun a i => a.push { var := i}) #[]
  for (_, f@⟨xs, s, _⟩) in p.constraints.toList do -- We could make a forIn instance for HashMap
    for i in [0:n] do
      let x := Coeffs.get xs i
      data := data.modify i fun d =>
        if x = 0 then
          { d with irrelevant := f :: d.irrelevant }
        else Id.run do
          let s' := s.scale x
          let mut d' := d
          if s'.lowerBound.isSome then
            d' := { d' with
              lowerBounds := (f, x) :: d'.lowerBounds
              lowerExact := d'.lowerExact && x.natAbs = 1 }
          if s'.upperBound.isSome then
            d' := { d' with
              upperBounds := (f, x) :: d'.upperBounds
              upperExact := d'.upperExact && x.natAbs = 1 }
          return d'
  return data

/--
Decides which variable to run Fourier-Motzkin elimination on, and returns the associated data.

We prefer eliminations which introduce no new inequalities, or otherwise exact eliminations,
and break ties by the number of new inequalities introduced.
-/
def fourierMotzkinSelect (data : Array FourierMotzkinData) : FourierMotzkinData := Id.run do
  let data := data.filter fun d => ¬ d.isEmpty
  let mut bestIdx := 0
  let mut bestSize := data[0]!.size
  let mut bestExact := data[0]!.exact
  if bestSize = 0 then return data[0]!
  for i in [1:data.size] do
    let exact := data[i]!.exact
    let size := data[i]!.size
    if size = 0 || !bestExact && exact || size < bestSize then
      if size = 0 then return data[i]!
      bestIdx := i
      bestExact := exact
      bestSize := size
  return data[bestIdx]!

/--
Run Fourier-Motzkin elimination on one variable.
-/
def fourierMotzkin (p : Problem) : Problem := Id.run do
  let data := p.fourierMotzkinData
  -- Now perform the elimination.
  let ⟨_, irrelevant, lower, upper, _, _⟩ := fourierMotzkinSelect data
  let mut r : Problem := { assumptions := p.assumptions, eliminations := p.eliminations }
  for f in irrelevant do
    r := r.insertConstraint f
  for ⟨f, b⟩ in lower do
    for ⟨g, a⟩ in upper do
      r := r.addConstraint (Fact.combo a f (-b) g).tidy
  return r

mutual

/--
Run the `omega` algorithm (for now without dark and grey shadows!) on a problem.
-/
partial def runOmega (p : Problem) : OmegaM Problem := do
  trace[omega] "Running omega on:\n{p}"
  if p.possible then
    let p' ← p.solveEqualities
    elimination p'
  else
    return p

/-- As for `runOmega`, but assuming the first round of solving equalities has already happened. -/
partial def elimination (p : Problem) : OmegaM Problem :=
  if p.possible then
    if p.isEmpty then
      return p
    else do
      trace[omega] "Running Fourier-Motzkin elimination on:\n{p}"
      runOmega p.fourierMotzkin
  else
    return p

end
