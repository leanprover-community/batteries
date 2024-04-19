/-
Copyright (c) 2018 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Mario Carneiro
-/

/-- A hash is lawful if elements which compare equal under `==` have equal hash. -/
class LawfulHashable (α : Type _) [BEq α] [Hashable α] : Prop where
  /-- Two elements which compare equal under the `BEq` instance have equal hash. -/
  hash_eq {a b : α} : a == b → hash a = hash b
