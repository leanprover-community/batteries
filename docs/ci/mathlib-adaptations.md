# Mathlib adaptation PRs

[Test Mathlib](../../.github/workflows/test_mathlib.yml) creates ordinary Mathlib PRs from a shared fork after successful Batteries CI.
The [contributor guide](../../README.md#mathlib-adaptations) explains how to supply adaptations.

## Setup and migration

Set up the fork and App, then transfer active branches before you enable the workflow:

1. Create `leanprover-community/mathlib4-adaptations` as a public fork of `mathlib4`.
   It must belong to Mathlib's GitHub fork network for normal fork PR CI to run.
   Leave Actions disabled in the fork. Mathlib runs the PR builds.
2. Register a private GitHub App named `batteries-mathlib-adaptations` under `leanprover-community`.
   Use the Batteries repository URL as its homepage. Disable webhooks; Actions runs the automation.
   Grant the App Contents, Workflows, and Pull requests write permissions. Keep other permissions at their defaults.
   Install it only on `mathlib4-adaptations` and `mathlib4`.
   Generate a private key and save it in the Batteries Actions secret `MATHLIB_ADAPTATIONS_PRIVATE_KEY`.
   Save the App ID in `MATHLIB_ADAPTATIONS_APP_ID`. Use a fresh key for this App.
   The workflow requests separate tokens for fork writes and Mathlib PR updates.
3. Configure the branch rules below, then grant the Batteries adaptation team write access to the fork.
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
   The adaptation workflow uses only the new App and secrets.
   Retire the old App and shared secrets after the remaining Lean nightly workflows have moved.

Complete the branch transfer before you enable the workflow.
If the fork lacks a PR's adaptation branch, the bot creates it from Mathlib `master`.

## Branch access

Use active [branch rulesets](https://docs.github.com/en/repositories/configuring-branches-and-merges-in-your-repository/managing-rulesets/creating-rulesets-for-a-repository)
with separate bypass lists for creation and updates:

| Target | Rule | Always-allowed bypass actors |
| --- | --- | --- |
| `batteries-*` | Restrict creations | `batteries-mathlib-adaptations` App |
| `batteries-*` | Restrict updates | The App and the Batteries adaptation team |
| All branches except `batteries-*` | Restrict creations and updates | Fork maintainers |
| All branches | Restrict deletions and block force pushes | Fork maintainers |

Each row is a separate ruleset. Disable any default rules not listed in that row.
Maintainers need a temporary creation bypass to transfer existing branches during migration.

Other Mathlib dependencies can share this fork with their own prefix, team, and App.
Add each prefix to the exclusions in the third ruleset and create its own creation and update rulesets.
Rules identify the App, not the repository that ran its workflow.
Keep each App's private key available only to its upstream repository.
Each upstream workflow supplies its dependency update and PR lifecycle; the fork runs no automation.

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

The first live lifecycle test requires the fork and App installation above.
