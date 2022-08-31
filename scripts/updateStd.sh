#!/bin/sh
# This command updates the `Std.lean` file to include a list of all files
# in the `Std` directory.
find Std -name "*.lean" | env LC_ALL=C sort \
  | sed 's/\.lean//;s,/,.,g;s/^/import /' > Std.lean
