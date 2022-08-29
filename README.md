# std4

Work in progress standard library for Lean 4. This is a collection of data structures and tactics intended for use by both computer-science applications and mathematics applications of Lean 4.

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
* If you added a new file, run the following command to update `Std.lean`
  ```
  find Std -name "*.lean" | env LC_ALL=C sort | sed 's/\.lean//;s,/,.,g;s/^/import /' > Std.lean
  ```
