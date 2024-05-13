/-
Copyright (c) 2024 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
open IO.Process
open System

/--
Run tests.

If no arguments are provided, run everything in the `test/` directory.

If arguments are provided, assume they are names of files in the `test/` directory,
and just run those.
-/
def main (args : List String) : IO Unit := do
  -- We first run `lake build`, to ensure oleans are available.
  -- Alternatively, we could use `lake lean` below instead of `lake env lean`,
  -- but currently with parallelism this results in build jobs interfering with each other.
  _ ← (← IO.Process.spawn { cmd := "lake", args := #["build"] }).wait
  -- Collect test targets, either from the command line or by walking the `test/` directory.
  let targets ← match args with
  | [] => System.FilePath.walkDir "./test"
  | _ => pure <| (args.map fun t => mkFilePath [".", "test", t] |>.withExtension "lean") |>.toArray
  let existing ← targets.filterM fun t => do pure <| (← t.pathExists) && !(← t.isDir)
  -- Generate a `lake env lean` task for each test target.
  let tasks ← existing.mapM fun t => do
    IO.asTask do
      let out ← IO.Process.output
        { cmd := "lake",
          args := #["env", "lean", t.toString],
          env := #[("LEAN_ABORT_ON_PANIC", "1")] }
      if out.exitCode = 0 then
        IO.println s!"Test succeeded: {t}"
      else
        IO.eprintln s!"Test failed: `lake env lean {t}` produced:"
        unless out.stdout.isEmpty do IO.eprintln out.stdout
        unless out.stderr.isEmpty do IO.eprintln out.stderr
      pure out.exitCode
  -- Wait on all the jobs and exit with 1 if any failed.
  let mut exitCode : UInt8 := 0
  for t in tasks do
    let e ← IO.wait t
    match e with
    | .ok 0 => pure ()
    | _ => exitCode := 1
  exit exitCode
