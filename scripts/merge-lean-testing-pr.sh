#!/usr/bin/env bash
set -eu

# This scripts merges a `lean-pr-testing-NNNN` branch into `nightly-testing`.
# This script is a copy of the same script in mathlib4, and should be kept in sync.
# Note that Mathlib uses `lakefile.lean`, while Batteries uses `lakefile.toml`

if [ "$#" -ne 1 ]; then
    echo "Usage: $0 <PR number>"
    exit 1
fi

PR_NUMBER=$1
BRANCH_NAME="lean-pr-testing-$PR_NUMBER"

git checkout nightly-testing
git pull --ff-only

if ! git merge origin/$BRANCH_NAME; then
    echo "Merge conflicts detected. Resolving conflicts in favor of current version..."
    git checkout --ours lean-toolchain lakefile.toml lake-manifest.json
    git add lean-toolchain lakefile.toml lake-manifest.json
fi

sed "s/$BRANCH_NAME/nightly-testing/g" < lakefile.toml > lakefile.toml.new
mv lakefile.toml.new lakefile.toml
git add lakefile.toml

# Check for merge conflicts
if git ls-files -u | grep -q '^'; then
    echo "Merge conflicts detected. Please resolve conflicts manually."
    git status
    exit 1
fi

if ! lake update; then
    echo "Lake update failed. Please resolve conflicts manually."
    git status
    exit 1
fi

# Add files touched by lake update
git add lakefile.toml lake-manifest.json

# Attempt to commit. This will fail if there are conflicts.
if git commit -m "merge $BRANCH_NAME"; then
    echo "Merge successful."
    git push
    echo "Pushed to github."
    exit 0
else
    echo "Merge failed. Please resolve conflicts manually and push to github."
    git status
    exit 1
fi
