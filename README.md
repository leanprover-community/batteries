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

Additionally, please make sure that you're using the version of Lean that the current version of `batteries` expects. The easiest way to do this is to copy the [`lean-toolchain`](./lean-toolchain) file from this repository to your project. Once you've added the dependency declaration, the command `lake update` checks out the current version of `batteries` and writes it the Lake manifest file. Don't run this command again unless you're prepared to potentially also update your Lean compiler version, as it will retrieve the latest version of dependencies and add them to the manifest.

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
documentation you need to run a HTTP server (e.g. `python3 -m http.server`) in the `docs/doc` directory.

Note that documentation for the latest nightly of `batteries` is also available as part of [the Mathlib 4
documentation][mathlib4 docs].

[mathlib4 docs]: https://leanprover-community.github.io/mathlib4_docs/Batteries.html

# Contributing

Every pull request should have exactly one of the status labels `awaiting-review`, `awaiting-author`
or `WIP` (in progress).
To change the status label of a pull request, add a comment containing one of these options and
_nothing else_.
This will remove the previous label and replace it by the requested status label.

One of the easiest ways to contribute is to find a missing proof and complete it. The
[`proof_wanted`](https://github.com/search?q=repo%3Aleanprover-community%2Fbatteries+language%3ALean+%2F^proof_wanted%2F&type=code)
declaration documents statements that have been identified as being useful, but that have not yet
been proven.

In contrast to Mathlib, Batteries uses pull requests from forks of this repository. Hence, no special permissions on this repository are required for new contributors.

You can change the labels on PRs by commenting one of `awaiting-review`, `awaiting-author`, or `WIP`. This is helpful for triage.

### Mathlib Adaptations

Batteries PRs often affect Mathlib, a key component of the Lean ecosystem.
When Batteries changes in a significant way, Mathlib must adapt promptly.
When necessary, Batteries contributors are expected to either create an adaptation PR on Mathlib, or ask for assistance for and to collaborate with this necessary process.

Every Batteries PR has an automatically created Mathlib branch called `batteries-pr-testing-N` where `N` is the number of the Batteries PR.
This is a clone of Mathlib where the Batteries requirement points to the Batteries PR branch instead of the main branch.
Batteries uses this branch to check whether the Batteries PR needs Mathlib adaptations.
A tag `builds-mathlib` will be issued when this branch needs no adaptation; a tag `breaks-mathlib` will be issued when the branch does need an adaptation.

The first step in creating an adaptation PR is to switch to the `batteries-pr-testing-N` branch and push changes to that branch until the Mathlib CI process works.
Changes to the Batteries PR will be integrated automatically as you work on this process.
Do not redirect the Batteries requirement to main until the Batteries PR is merged.
Please ask questions to Batteries and Mathlib maintainers if you run into issues with this process.

When everything works, create an adaptation PR on Mathlib from the `batteries-pr-testing-N` branch.
You may need to ping a Mathlib maintainer to review the PR, ask if you don't know who to ping.
Once the Mathlib adaptation PR and the original Batteries PR have been reviewed and accepted, the Batteries PR will be merged first. Then, the Mathlib PR's lakefile needs to be repointed to the Batteries main branch: change the Batteries line to
```lean
require "leanprover-community" / "batteries" @ git "main"
```
Once CI once again checks out on Mathlib, the adaptation PR can be merged using the regular Mathlib process.
