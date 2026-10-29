# Mathlib adaptation PRs

[Test Mathlib](../../.github/workflows/test_mathlib.yml) creates ordinary Mathlib PRs from a shared fork after successful Batteries CI.
The [contributor guide](../../README.md#mathlib-adaptations) explains how to supply adaptations.

## Setup and migration

Set up the fork and App, then transfer active branches before you enable the workflow:

1. Create `leanprover-community/mathlib4-batteries-adaptations` as a public fork of `mathlib4`.
   It must belong to Mathlib's GitHub fork network for normal fork PR CI to run.
   Leave Actions disabled in the fork. Mathlib runs the PR builds.
2. Give the Batteries adaptation contributors push access to the fork.
3. Install the `mathlib-nightly-testing` GitHub App on the fork and `mathlib4`.
   It needs Contents and Workflows write access on the fork, and Pull requests write access on Mathlib.
   The workflow requests separate tokens with these scopes.
   Keep the existing Batteries secrets, `MATHLIB_NIGHTLY_TESTING_APP_ID` and `MATHLIB_NIGHTLY_TESTING_PRIVATE_KEY`.
4. Pause the old Test Mathlib workflow for the cutover.
   Copy active `batteries-pr-testing-*` branches from `mathlib4-nightly-testing` to the new fork.
   Preserve their commit histories, including contributor adaptations. Do not overwrite an existing destination branch.
   Transfer any pending contributor fixes.
5. Merge the workflow change, then enable Test Mathlib again.
   Rerun successful Batteries CI for each active PR's current commit to create its draft Mathlib PR.
   Confirm that the PR names the new fork and that normal Mathlib CI starts.
   Link any original adaptation PRs from the new Mathlib PR.
6. After all active adaptations have moved, retire the old branches and merge the Mathlib reporter cleanup.
   Delete the migrated branches from nightly-testing so they stop receiving push builds.
   Use the Mathlib PR's checks for results.
   Remove stale `builds-mathlib` and `breaks-mathlib` labels from migrated Batteries PRs.

Complete the branch transfer before you enable the workflow.
If the fork lacks a PR's adaptation branch, the bot creates it from Mathlib `master`.

## Operation

An open Batteries PR uses the exact commit whose CI passed.
A merged Batteries PR uses `batteries @ main` and its current revision when Lake updates the manifest.
Dependency-only updates remain useful Mathlib PRs and are published normally.
The bot closes a Mathlib PR if its branch has no changes relative to `master`.

Updates preserve the adaptation branch history and merge Mathlib `master`.
The bot uses non-forced pushes to preserve concurrent contributor commits.
After a rejected push or an API failure, rerun all jobs in Test Mathlib to fetch the current branch commits.
For a merge conflict, resolve it on the adaptation branch first.

Reruns reuse the same open Mathlib PR.
Closed Mathlib PRs remain closed, including those merged by Bors.
If the Batteries PR reopens, ask a maintainer to reopen its Mathlib PR.
Then rerun successful Batteries CI.

Only the preparation job runs Lake. That job has no secrets, write token, or cache.
The other jobs treat its manifest as data.
The push token can write to the fork. A separate token can change PRs in Mathlib.

Workflow validation uses Actionlint and `.github/tests/test_mathlib.py` with Python, PyYAML, Node, Git, and jq.
The tests run the workflow's own scripts against temporary repositories and mocked GitHub responses.
The first live lifecycle test requires the fork and App installation above.
