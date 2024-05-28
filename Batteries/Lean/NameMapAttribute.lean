/-
Copyright (c) 2022 E.W.Ayers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: E.W.Ayers
-/
import Lean.Attributes

namespace Lean

/-- Maps declaration names to `α`. -/
def NameMapExtension (α : Type) := SimplePersistentEnvExtension (Name × α) (NameMap α)

instance : Inhabited (NameMapExtension α) :=
  inferInstanceAs <| Inhabited (SimplePersistentEnvExtension ..)

/-- Look up a value in the given extension in the environment. -/
def NameMapExtension.find? (ext : NameMapExtension α) (env : Environment) : Name → Option α :=
  (SimplePersistentEnvExtension.getState ext env).find?

/-- Add the given k,v pair to the NameMapExtension. -/
def NameMapExtension.add [Monad M] [MonadEnv M] [MonadError M]
  (ext : NameMapExtension α) (k : Name) (v : α) :  M Unit := do
  if let some _ := ext.find? (← getEnv) k then
    throwError "Already exists entry for {ext.name} {k}"
  else
     ext.addEntry (← getEnv) (k, v) |> setEnv

/-- Registers a new extension with the given name and type. -/
def registerNameMapExtension (α) (name : Name := by exact decl_name%) :
    IO (NameMapExtension α) := do
  registerSimplePersistentEnvExtension {
    name
    addImportedFn := fun ass =>
      ass.foldl (init := ∅) fun names as =>
        as.foldl (init := names) fun names (a, b) => names.insert a b
    addEntryFn    := fun s n => s.insert n.1 n.2
    toArrayFn     := fun es => es.toArray
  }

/-- The inputs to `registerNameMapAttribute`. -/
structure NameMapAttributeImpl (α : Type) where
  /-- The name of the attribute -/
  name : Name
  /-- The declaration which creates the attribute -/
  ref : Name := by exact decl_name%
  /-- The description of the attribute -/
  descr : String
  /-- This function is called when the attribute is applied.
  It should produce a value of type `α` from the given attribute syntax. -/
  add (src : Name) (stx : Syntax) : AttrM α
  deriving Inhabited

/-- Similar to `registerParametricAttribute` except that attributes do not
have to be assigned in the same file as the declaration. -/
def registerNameMapAttribute (impl : NameMapAttributeImpl α) : IO (NameMapExtension α) := do
  let ext ← registerNameMapExtension α impl.ref
  registerBuiltinAttribute {
    name := impl.name
    descr := impl.descr
    add := fun src stx _kind => do
      let a : α ← impl.add src stx
      ext.add src a
  }
  return ext
