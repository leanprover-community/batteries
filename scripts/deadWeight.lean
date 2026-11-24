import Batteries.Util.DeadWeight

open Lean Batteries.DeadWeight

/-- The help text of `deadWeight`. -/
def usage : String := "\
Usage: lake exe deadWeight MODULE ROOT... [--scope=PREFIX]...

Finds the parts of a development that some theorems do not use: modules, declarations, structure
fields, and predicates that are always true and have no alternative. Also lists the other
definitions that the theorems use but that ignore all of their arguments.

MODULE  a compiled module that imports the development, for example Main
ROOT    the full name of a theorem in MODULE or one of its imports
PREFIX  report only on the modules whose name starts with PREFIX
        (default: the first component of MODULE)

The results are candidates. A declaration can be absent from every proof term and still be needed
to elaborate one, for example as a simp lemma or in a macro. Before removing one, check that the
development still builds without it. Remove dead declarations and modules together."

/-- The axioms that are part of Lean's logic. -/
def standardAxioms : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]

/-- Prints a section of the report, unless it is empty. -/
def printSection (title : String) (lines : Array String) : IO Unit := do
  unless lines.isEmpty do
    IO.println s!"\n## {title} ({lines.size})"
    for line in lines do IO.println line

/-- Prints `report`. -/
def printReport (env : Environment) (report : Report) : IO Unit := do
  let located (name : Name) : String :=
    match env.getModuleIdxFor? name with
    | some idx => s!"{privateToUserName name} ({env.header.moduleNames[idx]!})"
    | none => s!"{privateToUserName name}"
  IO.println s!"The roots reach {report.numReached} constants, and \
    {report.numDecls - report.numDead} of the {report.numDecls} declarations in scope."
  printSection "Unexpected axioms (or theorems whose proofs are not loaded)" <|
    report.axioms.filter (!standardAxioms.contains ·) |>.map located
  printSection "Dead modules" <| report.deadModules.map toString
  printSection "Dead declarations in other modules" <| report.deadDecls.map located
  let (unsure, unread) := report.unreadFields.partition (·.destructured)
  let field (f : UnreadField) := located (f.structName ++ f.fieldName)
  printSection "Structure fields that are never read" <| unread.map field
  printSection "Structure fields that are never projected, in destructured structures \
    (inconclusive)" <| unsure.map field
  printSection "Propositions and predicates that are always true, and have no alternative \
    where they are used" <| report.vacuousPredicates.map fun (name, filled) =>
      let shown := ", ".intercalate (filled.toList.take 5 |>.map fun c => s!"{privateToUserName c}")
      let more := if filled.size > 5 then s!" and {filled.size - 5} more" else ""
      if filled.isEmpty then located name else s!"{located name}, as a parameter of {shown}{more}"
  printSection "Other reachable propositions and predicates that are constant" <|
    ← report.constantPredicates.mapM fun (name, msg) =>
      return s!"{located name} {← msg.toString}"
  printSection "Other reachable definitions that ignore all of their arguments" <|
    report.constantFunctions.map located

@[inherit_doc usage]
unsafe def main (args : List String) : IO UInt32 := do
  let (flags, names) := args.partition (·.startsWith "--")
  let scopes := flags.filterMap (·.dropPrefix? "--scope=" |>.map (·.toString.toName))
  let module :: roots := names.map String.toName | IO.eprintln usage; return 1
  if roots.isEmpty || scopes.length != flags.length then
    IO.eprintln usage
    return 1
  let scopes := if scopes.isEmpty then [module.getRoot] else scopes
  initSearchPath (← findSysroot)
  enableInitializersExecution
  -- The default level loads private data, which includes the proofs in files that use `module`.
  let env ← importModules #[{ module }] {} (trustLevel := 1024) (loadExts := true) (leakEnv := true)
  let inScopeModule := env.header.moduleNames.map fun mod => scopes.any (·.isPrefixOf mod)
  unless inScopeModule.contains true do
    IO.eprintln s!"no module of '{module}' is in scope: {scopes}"
    return 1
  let inScope (name : Name) : Bool := (env.getModuleIdxFor? name).any (inScopeModule[·]!)
  let (report, _) ← (analyze roots.toArray inScope).run'.toIO
    { fileName := "", fileMap := default, maxHeartbeats := 0 } { env }
  printReport env report
  return 0
