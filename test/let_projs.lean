import Std.Tactic.LetProjs
import Std.Data.Rat.Basic

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
  have : Foo := ‹_›
  trivial
