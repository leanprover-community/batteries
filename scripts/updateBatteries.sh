#!/bin/sh
set -e
# This command updates the `Batteries.lean` file to include a list of all files
# in the `Batteries` directory.
__LEAN_BATTERIES_AUTOFIX_IMPORTS=true lake env lean scripts/check_imports.lean
