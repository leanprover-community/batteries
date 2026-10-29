# Mathlib adaptation PRs

[Test Mathlib](../../.github/workflows/test_mathlib.yml) creates ordinary Mathlib PRs from a shared fork after successful Batteries CI.
The [contributor guide](../../README.md#mathlib-adaptations) explains how to supply adaptations.

## Repository and App

`leanprover-community/mathlib4-adaptations` is a public fork in Mathlib's GitHub fork network.
Actions is disabled in the fork. Mathlib runs the normal fork PR builds.

The `batteries-mathlib-adaptations` GitHub App is installed on the fork and `mathlib4`.
It has Contents, Workflows, and Pull requests write permissions.
The workflow uses the Batteries Actions secrets `MATHLIB_ADAPTATIONS_APP_ID` and `MATHLIB_ADAPTATIONS_PRIVATE_KEY`.
The App's private key is available only to Batteries.

The separate `mathlib-batteries-status` App has Pull requests write access to Batteries.
Mathlib uses it through the secrets `BATTERIES_STATUS_APP_ID` and `BATTERIES_STATUS_PRIVATE_KEY`.
This App reports CI results and has no access to write adaptation branches.

## Branch access

[Branch rulesets](https://docs.github.com/en/repositories/configuring-branches-and-merges-in-your-repository/managing-rulesets/about-rulesets)
control branch creation, updates, and deletion. Each row is a separate ruleset:

| Target | Rule | Always-allowed bypass actors |
| --- | --- | --- |
| `batteries-*` | Restrict creations | `batteries-mathlib-adaptations` App |
| `batteries-*` | Restrict updates | The App and the Batteries adaptation team |
| All branches except `batteries-*` | Restrict creations and updates | Fork maintainers |
| All branches | Restrict deletions and block force pushes | Fork maintainers |

Other Mathlib dependencies can share this fork with their own prefix, team, and App.
Each prefix has its own creation and update rulesets and is excluded from the rule for other branches.
Rules identify the App, not the repository that ran its workflow; each upstream holds only its own App's private key.
Each upstream workflow supplies its dependency update and PR lifecycle; the fork runs no automation.

## Operation

An open Batteries PR uses the exact commit whose CI passed.
A merged Batteries PR uses `batteries @ main` and its current revision when Lake updates the manifest.
Dependency-only updates remain useful Mathlib PRs and are published normally.
The bot closes a Mathlib PR if its branch has no changes relative to `master`.

The bot creates each adaptation branch from Mathlib `master`.
Later updates preserve the branch history and merge Mathlib `master`.
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

After the Mathlib build, tests, and lint finish, a separate GitHub-hosted job reports the results on the Batteries PR.
It maintains `builds-mathlib` and `breaks-mathlib` and appends results to its status comment, with links to the Mathlib PR and CI log.
An incomplete result clears both status labels.
If `awaiting-mathlib` is present, the job posts a fresh comment to notify subscribers; success removes that label.
The job skips superseded Mathlib commits and outdated Batteries pins.
It reads the manifest as data and runs no PR code with the reporting token.
