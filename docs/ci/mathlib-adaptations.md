# Mathlib adaptation workflow

Batteries dispatches `batteries-pr-validation.yml` in `leanprover-community/downstream-reports` and waits for its result.
The initial build and all dependency preparation run there. Batteries receives no access to the self-hosted runner pool.
The new workflow shares the queue with `mathlib-pr-validation.yml` and uses the same isolated `pr` runners.

## Behavior

New PRs and new head revisions receive `mathlib-not-checked`. Its description appears in the label tooltip:

> Mathlib has not been checked for this revision. Comment !adaptations to request a check.

The PR author or a user with triage or write access can post `!adaptations` on a standalone line.
The command adds `mathlib-adaptations`, which opts the PR in to checks across subsequent updates.
A maintainer can add that label directly. Removing it disables future dispatches and publication of an in-flight result.
The workflow creates these labels if needed and keeps their descriptions current.

A request after CI passes starts immediately. A request during CI waits for a successful CI run at the current head.
Unrequested PRs do not dispatch builds. Duplicate CI events skip a validation already completed for both pinned revisions.
Another `!adaptations` command requests a fresh check.

1. Successful Batteries CI selects an opted-in PR to `main` at the tested head SHA.
2. The bot pins Mathlib `master` and the Batteries head to exact revisions.
3. Batteries dispatches a downstream run with a unique request ID, then waits for that exact run.
4. With no existing adaptation PR, downstream-reports builds Mathlib, Archive, and Counterexamples.
5. A successful build reports `builds-mathlib`. It creates no adaptation PR and uploads no cache.
6. A failed build returns a Git bundle. A fresh Batteries publisher opens a draft Mathlib PR from the adaptation fork.
7. Once the draft exists, subsequent dispatches refresh its dependency and preserve adaptation commits.
   Ordinary Mathlib fork CI performs subsequent tests and cache uploads.

The initial check tests compilation, not the complete Mathlib test and lint suite.
Matching build results replace `mathlib-not-checked` with `builds-mathlib` or `breaks-mathlib`.
A branch refresh alone keeps the unchecked label until ordinary Mathlib CI returns a matching result.
Setup errors, missing results, cancellation, and timeout cannot open an adaptation PR.
The controller checks the request ID, PR number, repositories, and both commit SHAs in the returned result.
It renews the App token during long queue waits. It waits up to 285 minutes, then cancels the identified downstream run.
A later Batteries CI rerun can retry a timed-out request.

The dependency job has read-only credentials and no App tokens, CI secrets, or cache upload credentials.
It uses `lake --keep-toolchain update batteries` so Lake retains Mathlib's compiler.
The publisher reads a bounded JSON result and fetches Git objects. It does not execute the candidate tree.
A normal push rejects concurrent human edits. The bot never force-pushes.
Conflicts with Mathlib `master` require a maintainer to resolve them.

## Resources to create or configure

- Merge [downstream-reports #101](https://github.com/leanprover-community/downstream-reports/pull/101) before this Batteries workflow becomes active.
  The companion workflow is `batteries-pr-validation.yml`; its run name includes the request ID.
  Both downstream PR workflows use `queue: max` in the `mathlib-pr-validation` concurrency group.
  Up to 100 pending runs can wait without a newer dispatch replacing them.
- Create a public fork of Mathlib, provisionally `leanprover-community/mathlib4-adaptations`.
  Grant access to the adaptation maintainers. Disable inherited scheduled and push CI in this fork.
  Mathlib's base-repository fork workflow supplies CI.
- Set `MATHLIB_ADAPTATION_FORK` in Batteries to `mathlib4-adaptations`, or the chosen fork name.
  The workflow requires a dedicated fork in `leanprover-community`.
- Install the existing Mathlib nightly-testing GitHub App on downstream-reports and the adaptation fork.
  It needs Actions write and Contents read on downstream-reports, Contents write on the fork, and Pull requests write on Mathlib.
  Each controller or publisher token requests only the permissions for its target repository.
  Reuse `MATHLIB_NIGHTLY_TESTING_APP_ID` and `MATHLIB_NIGHTLY_TESTING_PRIVATE_KEY` in Batteries.
  No downstream token-mint environment or new Azure identity is needed for the initial build.
- Add a trusted Mathlib result reporter for fork PRs from `adaptations/batteries-N` in the configured fork.
  The reporter runs on a fresh runner after CI. It must not execute the candidate tree with its App token.
  Give its App Contents write on Batteries so it can send a repository dispatch.
  Set `MATHLIB_ADAPTATION_REPORTER_BOT` in Batteries to that App's bot login, including `[bot]`.
  The existing App can serve this role if its installation and token source support those permissions.

No new runner registrations, Batteries runner access, cache containers, or cache upload credentials are required.
The request workflow uses Batteries' own `GITHUB_TOKEN` for labels and its local workflow dispatch.
The new branch prefix avoids the cache client's special routing for `batteries-pr-testing-*`.

## Ordinary Mathlib CI reporter contract

The companion Mathlib reporter remains a required resource to create.
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

Merge the downstream companion, create the fork, update the App installation, and add the Mathlib reporter before this draft merges.
Existing nightly-testing branches are not migrated automatically.
Move active adaptations separately. Remove the old `batteries-pr-testing-*` reporting hooks after that migration.
Retire `pr-toolchain-tests` only after all remaining producers and readers have been checked.
