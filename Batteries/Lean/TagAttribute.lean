/-
Copyright (c) 2022 Gabriel Ebner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Ebner
-/
module

public import Lean.Attributes

public section

/-- Get the list of declarations tagged with the tag attribute `attr`. -/
@[expose] def Lean.TagAttribute.getDecls (attr : TagAttribute) (env : Environment) : Array Name :=
  core <| attr.ext.toEnvExtension.getState env
where
  /-- Implementation of `TagAttribute.getDecls`. -/
  core (st : PersistentEnvExtensionState Name NameSet) : Array Name := Id.run do
    let mut decls := st.state.toArray
    for ds in st.importedEntries do
      decls := decls ++ ds
    decls
