#!/bin/sh
# This command updates the `Std.lean` file to include a list of all files
# in the `Std` directory.
__LEAN_STD_AUTOFIX_IMPORTS=true lake env lean test/check_imports_std_data.lean
lake build
