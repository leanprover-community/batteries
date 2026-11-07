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

# Batteries Cell Network (Experimental)

The Batteries Cell Network consists of independent repositories that can be safely imported along with Batteries.
These repositories are supported by Batteries maintainers to make sure that they are up to date and compatible with each other.

Current cells include:

* [leanprover-community/batteries-cell-template](https://github.com/leanprover-community/batteries-cell-template):
  A template for creating new cells.

* [leanprover-community/batteries-recycling](https://github.com/leanprover-community/batteries-recycling):
  Storage for obsolescent modules from Batteries.

* [fgdorais/batteries-kmp](https://github.com/fgdorais/batteries-kmp):
  General purpose implementation of the Knuth-Morris-Pratt (KMP) matching algorithm.

* [fgdorais/batteries-finite-streams](https://github.com/fgdorais/batteries-finite-streams):
  Finite streams, stream combinators and stream iterators.

The Batteries Cell Network is not yet open to external contributions.

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
When necessary, Batteries contributors are expected to either create an adaptation PR, or ask for assistance for and to collaborate with this necessary process.

Every Batteries PR has an automatically created [Mathlib Adaptations](https://github.com/leanprover-community/mathlib4-adaptations/) branch called `batteries-pr-testing-N` where `N` is the number of the Batteries PR.
This is a clone of Mathlib where the Batteries requirement is pinned to the PR commit whose
Batteries CI succeeded, instead of following the main branch.
A draft adaptation PR from this branch to Mathlib is opened automatically, and Mathlib CI tests it like any other Mathlib PR.
It is kept as a draft until the Batteries PR is merged.
Batteries uses this PR to check whether the Batteries PR needs Mathlib adaptations.
A tag `builds-mathlib` will be issued when this PR needs no adaptation; a tag `breaks-mathlib` will be issued when the PR does need an adaptation.

To adapt Mathlib:

1. Fork [Mathlib Adaptations](https://github.com/leanprover-community/mathlib4-adaptations/).
   If you already have a fork of Mathlib, you can use it, because both repositories are in the same fork network.
2. In your Mathlib checkout, create a branch from `batteries-pr-testing-N`, where `N` is the number of the Batteries PR, and get the Mathlib cache:
   ```sh
   git remote add adaptations https://github.com/leanprover-community/mathlib4-adaptations.git
   git fetch adaptations batteries-pr-testing-N
   git switch -c my-adaptation --track adaptations/batteries-pr-testing-N
   lake exe cache get
   ```
   The branch tracks Mathlib Adaptations, so `lake exe cache get` downloads the files that Mathlib CI built for the adaptation PR.
   If Mathlib CI has not finished on the latest commit, run the command again after it finishes.
3. Commit your changes and push the branch to your fork with `git push origin my-adaptation`, where `origin` is your fork.
   You will need this invocation because your branch tracks Mathlib Adaptations, so a plain `git push` will try to push there, and you cannot push to Mathlib Adaptations.
4. From your fork, open a PR to the branch `batteries-pr-testing-N`.
   Do not change the Batteries requirement yourself.
5. Post a comment on your original Batteries PR that your PR is ready for review.

A Batteries maintainer will then review your PR and merge it into `batteries-pr-testing-N`.
CI runs only on the adaptation PR, after your changes are merged into the branch.
Changes to the Batteries PR will be integrated automatically, and merged adaptation commits are kept.
If the branch conflicts with Mathlib `master`, merge `master` in your PR and resolve the conflicts there.

Once the Batteries PR is merged, the Batteries requirement is repointed to the main branch and the adaptation PR is marked ready for review.
The bot then comments on both PRs and mentions the Batteries maintainer who merged the Batteries PR.
It can then be merged using the regular Mathlib process. You may need to ping a Mathlib maintainer to review the PR.
If the Batteries PR is closed without being merged, or the adaptation PR changes only the Batteries version, the adaptation PR is closed.
In the second case, the bot comments on both PRs that no adaptations were pushed.

If the bot fails to update the branch or the adaptation PR after a rejected push or an API error, a Batteries maintainer can rerun all jobs of the Test Mathlib workflow.
After a merge or a close, the bot posts a comment on the Batteries PR when the update fails.
If a closed Batteries PR is reopened, a Mathlib maintainer must reopen its adaptation PR before the next Batteries CI run.

Please ask questions to Batteries maintainers if you run into issues with this process.
