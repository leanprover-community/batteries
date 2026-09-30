# Mathlib adaptation workflow

This draft replaces the `batteries-pr-testing-*` push workflow with an initial build and ordinary Mathlib PRs.
Its build job follows the separation in
[downstream-reports/mathlib-pr-validation.yml](https://github.com/leanprover-community/downstream-reports/blob/main/.github/workflows/mathlib-pr-validation.yml).
That workflow cannot be called directly: it uses `workflow_dispatch` and requires an existing Mathlib PR merge SHA.
Here, the initial build needs no Mathlib PR. It runs in Batteries with the same `pr` runner pool.

## Behavior

1. A successful Batteries CI run selects an open PR to `main` at the tested head SHA.
2. The bot pins Mathlib `master` and the Batteries head to exact revisions.
3. With no existing adaptation PR, a job builds Mathlib, Archive, and Counterexamples.
4. A successful build reports `builds-mathlib` without a branch push or cache upload.
5. A failed build transfers a Git bundle to a fresh publisher. The publisher opens a draft Mathlib PR.
6. Once the draft exists, the bot refreshes its dependency. Ordinary fork CI performs subsequent tests and cache uploads.

The initial build checks compilation. It does not run the complete Mathlib test and lint suite.
Setup failures stop the workflow. They do not open an adaptation PR or report a compilation failure.
The dependency job has read-only credentials. It receives no App tokens or cache upload credentials.
It uses `lake --keep-toolchain update batteries` so Lake cannot select a different compiler during the update.
The publisher does not execute the candidate tree. A normal push rejects concurrent edits; the bot never force-pushes.
Conflicts with Mathlib `master` require a maintainer to resolve them.

## Resources to create or configure

- Create a public fork of `leanprover-community/mathlib4`, provisionally `leanprover-community/mathlib4-adaptations`.
  Give the adaptation maintainers write access. Disable inherited scheduled and push CI in this fork.
  Mathlib's base-repository fork workflow supplies CI.
- Set the Batteries repository variable `MATHLIB_ADAPTATION_FORK` to `mathlib4-adaptations`, or the chosen fork name.
  The workflow requires a dedicated fork in `leanprover-community`.
- Give Batteries access to the isolated self-hosted runners with the `pr` label.
  Use the pool that supports arbitrary dependency builds without regression-side secrets.
- Install the existing Mathlib nightly-testing GitHub App on the new fork.
  It needs Contents write on the fork and Pull requests write on Mathlib.
  The publisher requests separate tokens with these permissions.
  Reuse the existing Batteries secrets `MATHLIB_NIGHTLY_TESTING_APP_ID` and `MATHLIB_NIGHTLY_TESTING_PRIVATE_KEY`.
- Add a trusted Mathlib result reporter for fork PRs from `adaptations/batteries-N` in this fork.
  The reporter runs on a fresh runner after CI. It must not execute the candidate tree with its App token.
  Give its App Contents write on Batteries so it can send a repository dispatch.
  Set `MATHLIB_ADAPTATION_REPORTER_BOT` in Batteries to that App's bot login, including `[bot]`.
  The existing App can serve this role if its installation and token source support those permissions.

No new cache container, cache writer identity, or Azure/R2 upload credential is required.
The initial check publishes no public cache. Adaptation PRs use the existing ordinary fork cache path.
The new branch prefix avoids the cache client's special routing for `batteries-pr-testing-*`.

## Result reporter contract

The companion Mathlib reporter is a required resource that this draft does not create.
Send `repository_dispatch` to `leanprover-community/batteries` with `event_type: mathlib-adaptation-result`.
Its `client_payload` has these fields:

```json
{
  "batteries_pr_number": 123,
  "batteries_sha": "<40-character Batteries commit SHA>",
  "mathlib_pr_number": 456,
  "mathlib_sha": "<40-character Mathlib PR head SHA>",
  "result": "success"
}
```

Derive the Batteries PR number from the validated head branch and fork repository.
Read the Batteries revision from `lake-manifest.json` at the Mathlib revision that CI actually tested.
Use the captured PR head SHA, not `github.sha` from `pull_request_target`.
Send `success` or `failure` for the build, test, and lint results.
Do not send a result for cancelled runs or an infrastructure failure.
The Batteries receiver checks the sender and both current PR revisions before it changes feedback.
The receiver updates one bot comment and the existing `builds-mathlib` or `breaks-mathlib` label.

## Rollout

Create the fork, configure runner access, update the App installation, and add the Mathlib reporter before this draft merges.
Existing nightly-testing branches are not migrated automatically.
Close or archive them separately after their active adaptations move to the new fork.
Remove the old Mathlib `batteries-pr-testing-*` reporting hooks after that migration.
Retire `pr-toolchain-tests` only after all remaining producers and readers have been checked.
