# std4

Work in progress standard library for Lean 4. This is a collection of data structures and tactics intended for use by both computer-science applications and mathematics applications of Lean 4.

# Using `std4`

To use `std4` in your project, add the following to your `lakefile.lean`:

```lean
require std from git "git@github.com:leanprover/std4.git" @ "main"
```

Additionally, please make sure that you're using the version of Lean that the current version of `std4` expects. The easiest way to do this is to copy the [`lean-toolchain`](./lean-toolchain) file from this repository to your project. Once you've added the dependency declaration, the command `lake update` checks out the current version of `std4` and writes it the Lake manifest file. Don't run this command again unless you're prepared to potentially also update your Lean compiler version, as it will retrieve the latest version of dependencies and add them to the manifest.

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
* To build `std4` run `lake build`. To build and run all tests, run `make`.
* If you added a new file, run the following command to update `Std.lean`:
  ```
  find Std -name "*.lean" | env LC_ALL=C sort | sed 's/\.lean//;s,/,.,g;s/^/import /' > Std.lean
  ```
  (or use `scripts/updateStd.sh` which contains this command).

# Documentation

You can generate `std4`'s documentation with

```text
# if you're generating documentation for the first time
> lake -Kdoc=on update
...
# actually generate the documentation
> lake -Kdoc=on build Std:docs
...
> ls build/doc/index.html
build/doc/index.html
```

The top-level HTML file will be located at `build/doc/Std.html`, though to actually expose the
documentation as a server you need to

```text
> cd build/doc
> python3 -m http.server
Serving HTTP on :: port 8000 (http://[::]:8000/) ...
```

Note that documentation for the latest nightly of `std4` is available as part of [the Mathlib 4
documentation][mathlib4 docs].

[mathlib4 docs]: https://leanprover-community.github.io/mathlib4_docs/Std.html
