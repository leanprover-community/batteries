#!/usr/bin/env bash
set -euo pipefail

branch="adaptations/batteries-$PR_NUMBER"
cd mathlib
git config user.name 'mathlib-nightly-testing[bot]'
git config user.email 'mathlib-nightly-testing[bot]@users.noreply.github.com'
git remote add adaptations "https://github.com/leanprover-community/$ADAPTATION_FORK.git"

if [ -n "$ADAPTATION_PR" ]; then
  git fetch adaptations "refs/heads/$branch:refs/remotes/adaptations/current"
  git switch -c "$branch" refs/remotes/adaptations/current
  # Preserve adaptations. Stop on conflicts so a maintainer can resolve them.
  git merge "$MATHLIB_SHA" --no-edit
else
  git switch -c "$branch" "$MATHLIB_SHA"
fi

python3 - <<'PY'
import os
import re
from pathlib import Path

path = Path('lakefile.lean')
replacement = (f'require "leanprover-community" / "batteries" from git '
               f'"https://github.com/{os.environ["BATTERIES_REPO"]}" '
               f'@ "{os.environ["BATTERIES_SHA"]}"')
text, count = re.subn(r'^require "leanprover-community" / "batteries"[^\n]*$',
                      lambda _: replacement, path.read_text(), flags=re.MULTILINE)
if count != 1:
    raise SystemExit('Expected exactly one Batteries requirement')
path.write_text(text)
PY

# Install the toolchain selected by Mathlib, not by the Batteries PR.
if ! command -v elan >/dev/null; then
  curl -sSfL https://github.com/leanprover/elan/releases/download/v3.0.0/elan-x86_64-unknown-linux-gnu.tar.gz \
    | tar xz -C "$RUNNER_TEMP"
  "$RUNNER_TEMP/elan-init" -y --default-toolchain none
fi
export PATH="$HOME/.elan/bin:$PATH"
echo "$HOME/.elan/bin" >> "$GITHUB_PATH"
lake --keep-toolchain update batteries
git add lakefile.lean lake-manifest.json
git commit --allow-empty -m "chore: test Batteries PR #$PR_NUMBER at $BATTERIES_SHA"

# Transfer Git objects to a fresh publisher. This is not a public cache.
git bundle create "$RUNNER_TEMP/mathlib-adaptation.bundle" "refs/heads/$branch" "^$MATHLIB_SHA"

if [ -z "$ADAPTATION_PR" ]; then
  # Read the regular public cache before the initial build. Do not publish it.
  lake exe cache get --repo=leanprover-community/mathlib4
fi
