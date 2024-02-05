import Std.Tactic.LetProjs
import Std.Data.Rat.Basic

open Lean.Elab.Tactic

-- We define a syntactic frontend for `Lean.MVarId.letProjs`, just for testing.
-- The tactic is only intended for use by other tactics,
-- so we don't want a public syntactic frontend.

/--
`let_projs` adds let bindings for all projections of local hypotheses, recursively.

For example in
```
example (x : Nat × Nat × Nat) : True := by
  let_projs
  trivial
```
we have
```
x_fst: ℕ := x.1
x_snd: ℕ × ℕ := x.2
x_snd_fst: ℕ := x_snd.1
x_snd_snd: ℕ := x_snd.2
```

`let_projs h₁ h₂` only adds let bindings for projections of the specified hypotheses.
-/
syntax (name := let_projs_syntax) "let_projs" (ppSpace colGt ident)* : tactic

@[inherit_doc let_projs_syntax]
elab_rules : tactic | `(tactic| let_projs $hs:ident*) => do
  let hs ← getFVarIds hs
  if hs.isEmpty then
    liftMetaTactic fun g => return [← g.letProjsAll]
  else
    liftMetaTactic fun g => return [← g.letProjs hs]

structure R where
  x : Nat
  y : Int

structure S extends R where
  z : Rat

example (x : Nat × Nat × Nat) : True := by
  let_projs
  trivial

example (s : S) (x : Nat × Nat) : Nat := by
  let_projs x
  clear s -- check that we didn't create let bindings mentioning `s`
  exact x_fst

example (s : S) (x : Nat × Nat) : Nat := by
  let_projs
  exact s_z_den + x_snd

class Foo
class Bar extends Foo

example [Bar] : True := by
  let_projs
  fail_if_success have : Foo := ‹_›
  trivial
