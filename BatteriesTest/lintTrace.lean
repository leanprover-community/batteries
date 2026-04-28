import Batteries.Tactic.Lint

/-!
Tests tracing in `#lint`.

Note that this does not test tracing in `runLinter` per se.
-/

-- oops, no docstring
def foo := 3

theorem bar : foo = 3 := rfl

set_option trace.Batteries.Lint true

/--
trace: [Batteries.Lint] Running linters:
      docBlame
[Batteries.Lint] - docBlame: (0/2) Starting...
[Batteries.Lint] - docBlame: (1/2) Getting...
[Batteries.Lint] - docBlame: (2/2) Failed with 1 messages.
[Batteries.Lint] Completed linting!
-/
#guard_msgs (trace, drop error) in
#lint- only docBlame

/--
trace: [Batteries.Lint] Running linters:
      defLemma
[Batteries.Lint] - defLemma: (0/2) Starting...
[Batteries.Lint] - defLemma: (1/2) Getting...
[Batteries.Lint] - defLemma: (2/2) Passed!
[Batteries.Lint] Completed linting!
-/
#guard_msgs in
#lint- only defLemma
