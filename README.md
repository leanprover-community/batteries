# Batteries

The "batteries included" extended library for Lean 4. This is a collection of data structures and tactics intended for use by both computer-science applications and mathematics applications of Lean 4.

# Using `batteries`

To use `batteries` in your project, add the following to your `lakefile.lean`:

```lean
require batteries from git "https://github.com/leanprover-community/batteries" @ "main"
```

Additionally, please make sure that you're using the version of Lean that the current version of `batteries` expects. The easiest way to do this is to copy the [`lean-toolchain`](./lean-toolchain) file from this repository to your project. Once you've added the dependency declaration, the command `lake update` checks out the current version of `batteries` and writes it the Lake manifest file. Don't run this command again unless you're prepared to potentially also update your Lean compiler version, as it will retrieve the latest version of dependencies and add them to the manifest.

# Build instructions

* Get the newest version of `elan`. If you already have installed a version of Lean, you can run
  ```
  elan self update
  ```
  If the above command fails, or if you need to install `elan`, run
  ```
  curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh
  ```
  If this also fails, follow the instructions under `Regular install` [here](https://leanprover-community.github.io/get_started.html).
* To build `batteries` run `lake build`. To build and run all tests, run `make`.
* If you added a new file, run the command `scripts/updateBatteries.sh` to update the
  imports.

# Documentation

You can generate `batteries`' documentation with

```text
# if you're generating documentation for the first time
> lake -R -Kdoc=on update
...
# actually generate the documentation
> lake -R -Kdoc=on build Batteries:docs
...
> ls build/doc/index.html
build/doc/index.html
```

After generating the docs, run `lake build -R` to reset the configuration.

The top-level HTML file will be located at `build/doc/Batteries.html`, though to actually expose the
documentation as a server you need to

```text
> cd build/doc
> python3 -m http.server
Serving HTTP on :: port 8000 (http://[::]:8000/) ...
```

Note that documentation for the latest nightly of `batteries` is available as part of [the Mathlib 4
documentation][mathlib4 docs].

[mathlib4 docs]: https://leanprover-community.github.io/mathlib4_docs/Batteries.html

# Contributing

Every pull request should have exactly one of the status labels `awaiting-review`, `awaiting-author`
or `WIP` (in progress).
To change the status label of a pull request, add a comment containing one of these options and
_nothing else_.
This will remove the previous label and replace it by the requested status label.

One of the easiest ways to contribute is to find a missing proof and complete it. The
[`proof_wanted`](https://github.com/search?q=repo%3Aleanprover-community%2Fbatteries+proof_wanted+language%3ALean&type=code&l=Lean)
declaration documents statements that have been identified as being useful, but that have not yet
been proven.

In contrast to mathlib, `batteries` uses pull requests from forks of this repository. Hence, no special permissions on this repository are required for new contributors.

You can change the labels on PRs by commenting one of `awaiting-review`, `awaiting-author`, or `WIP`. This is helpful for triage.
