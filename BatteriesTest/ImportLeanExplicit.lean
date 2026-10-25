module

public import Batteries
public import Lean.Expr

-- Counterpart to `BatteriesTest/ImportLean.lean`: adding an ordinary `Lean.Expr` import
-- makes the runtime definition rejected there valid here.
public def foo : Lean.Expr := .bvar 0
