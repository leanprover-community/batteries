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

Batteries PRs often affect Mathlib, a key component of the Lean ecosystem.
When Batteries changes in a significant way, Mathlib must adapt promptly.
When necessary, Batteries contributors are expected to either create an adaptation PR on Mathlib, or ask for assistance for and to collaborate with this necessary process.

New PR revisions receive a `mathlib-not-checked` label. Its tooltip explains how to request a check.
The PR author or a user with triage or write access can comment `!adaptations` on a line by itself.
Maintainers can also add the `mathlib-adaptations` label directly.
The request opts the PR in to Mathlib checks for subsequent updates.
Remove `mathlib-adaptations` to disable those checks.

After the request and successful Batteries CI, the bot dispatches a build in `downstream-reports` and waits for its result.
The build tests the exact PR revision against Mathlib `master`.
The initial check builds Mathlib, Archive, and Counterexamples with Mathlib's toolchain.
It reads the public cache and does not upload a cache.
If the build passes, the bot applies the `builds-mathlib` label. No adaptation PR is needed.
The `mathlib-not-checked` label clears when the check returns a matching result.

If the build fails, the bot opens a draft Mathlib PR and applies the `breaks-mathlib` label.
The PR uses `adaptations/batteries-N` in the configured adaptation fork, where `N` is the Batteries PR number.
The bot posts the PR link on the Batteries PR. Make the Mathlib adaptations on that branch.
Ask a maintainer for access to the adaptation fork if needed.
Later successful Batteries CI runs update the dependency and preserve the adaptation commits.
Ordinary Mathlib fork CI tests the branch and publishes its SHA-scoped cache.
Its results update the Batteries labels and comment through the result reporter.

Keep the Mathlib PR in draft until the Batteries PR has merged.
Then restore the Batteries requirement to `main`:
```lean
require "leanprover-community" / "batteries" @ git "main"
```
Run `lake update batteries` and commit the manifest update.
Close the draft if no Mathlib adaptations remain. Otherwise, request Mathlib review after CI passes.

See [the setup requirements](docs/ci/mathlib-adaptations.md) for the resources required by these workflows.
