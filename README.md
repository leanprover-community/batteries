# Batteries

The "batteries included" extended library for Lean 4. This is a collection of data structures and tactics intended for use by both computer-science applications and mathematics applications of Lean 4.

# Using `batteries`

To use `batteries` in your project, add the following to your `lakefile.lean`:
```lean
require "leanprover-community" / "batteries" @ git "main"
```
Or add the following to your `lakefile.toml`:
```toml
[[require]]
name = "batteries"
scope = "leanprover-community"
rev = "main"
```

Additionally, please make sure that you're using the version of Lean that the current version of `batteries` expects. The easiest way to do this is to copy the [`lean-toolchain`](./lean-toolchain) file from this repository to your project. Once you've added the dependency declaration, the command `lake update` checks out the current version of `batteries` and writes it to the Lake manifest file. Don't run this command again unless you're prepared to potentially also update your Lean compiler version, as it will retrieve the latest version of dependencies and add them to the manifest.

# Build instructions

* Get the newest version of `elan`. If you already have installed a version of Lean, you can run
  ```sh
  elan self update
  ```
  If the above command fails, or if you need to install `elan`, run
  ```sh
  curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh
  ```
  If this also fails, follow the instructions under `Regular install` [here](https://leanprover-community.github.io/get_started.html).
* To build `batteries` run `lake build`.
* To build and run all tests, run `lake test`.
* To run the environment linter, run `lake lint`.
* If you added a new file, run the command `scripts/updateBatteries.sh` to update the imports.

# Documentation

You can generate `batteries` documentation with

```sh
cd docs
lake build Batteries:docs
```

The top-level HTML file will be located at `docs/doc/index.html`, though to actually expose the
documentation you need to run an HTTP server (e.g. `python3 -m http.server`) in the `docs/doc` directory.

Note that documentation for the latest nightly of `batteries` is also available as part of [the Mathlib 4
documentation][mathlib4 docs].

[mathlib4 docs]: https://leanprover-community.github.io/mathlib4_docs/Batteries.html

# Contributing

The first step to contribute is to create a fork of Batteries.
Then add your contributions to a branch of your fork and make a PR to Batteries.
Do not make your changes to the main branch of your fork, that may lead to complications on your end.

Every pull request should have exactly one of the status labels `awaiting-review`, `awaiting-author`
or `WIP` (in progress).
To change the status label of a pull request, add a comment containing one of these options and
_nothing else_.
This will remove the previous label and replace it by the requested status label.
These labels are used for triage.

One of the easiest ways to contribute is to find a missing proof and complete it. The
[`proof_wanted`](https://github.com/search?q=repo%3Aleanprover-community%2Fbatteries+language%3ALean+%2F^proof_wanted%2F&type=code)
declaration documents statements that have been identified as being useful, but that have not yet
been proven.

### Mathlib Adaptations

Batteries contributors must help adapt Mathlib when their changes require it.
Ask a Batteries maintainer for help if you need it.

After a Batteries PR to `main` passes CI, the bot opens a draft PR against Mathlib's `master`.
Its branch is `batteries-pr-testing-N` in
[mathlib4-adaptations](https://github.com/leanprover-community/mathlib4-adaptations),
where `N` is the Batteries PR number.
The bot pins the Batteries dependency to the commit that passed CI and updates it after subsequent successful runs.
Mathlib's normal fork CI checks the draft PR. Read its checks for the results.

To supply adaptations:

1. Ask a Batteries maintainer for push access to the `batteries-*` branches in `mathlib4-adaptations` if you need it.
2. Push your Mathlib changes to `batteries-pr-testing-N` in that repository.
   If you do not have push access, open a PR from your Mathlib fork to that branch.
3. Check the Mathlib PR's CI and tell the Batteries maintainer when the adaptations are ready.

The bot preserves your commits when it updates the dependency.
It manages only the Batteries dependency. Coordinate other dependency changes and review blockers with the maintainers.

After the Batteries PR merges, the bot restores `batteries @ main` and updates the manifest.
It then marks the open Mathlib PR ready for review, including PRs that only update the dependency.
If no changes remain relative to Mathlib's `master`, the bot closes the Mathlib PR instead.
It also closes the Mathlib PR if the Batteries PR closes without a merge.

If the Batteries PR reopens, ask a maintainer to reopen its Mathlib PR.
Then rerun successful Batteries CI.

The [CI setup notes](docs/ci/mathlib-adaptations.md) describe the fork, App permissions, branch rules, and migration.
