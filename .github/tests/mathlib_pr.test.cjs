const { test } = require('node:test');
const assert = require('node:assert/strict');
const { readFileSync } = require('node:fs');
const AsyncFunction = Object.getPrototypeOf(async function () {}).constructor;
const run = new AsyncFunction('github', readFileSync(process.env.LIFECYCLE_SCRIPT, 'utf8'));
const sha = 'a'.repeat(40);
const fork = 'leanprover-community/mathlib4-batteries-adaptations';
const pr = { number: 100, node_id: 'PR_100', state: 'open', draft: true, head: { repo: { full_name: fork } } };

async function scenario({ state = 'open', prs = [], changes = true, currentState = state, currentSHA = sha } = {}) {
  Object.assign(process.env, { PR_NUMBER: '42', PR_STATE: state, BATTERIES_SHA: sha, HAS_CHANGES: String(changes) });
  const calls = [];
  const github = {
    rest: { pulls: {
      get: async () => ({ data: { state: currentState === 'merged' ? 'closed' : currentState,
        merged: currentState === 'merged', base: { ref: 'main' }, head: { sha: currentSHA } } }),
      list: 'list',
      create: async data => calls.push(['create', data]),
      update: async data => calls.push(['update', data]),
    } },
    paginate: async () => prs,
    graphql: async (query, data) => calls.push([query.includes('markPullRequestReadyForReview') ? 'ready' : 'draft', data]),
  };
  await run(github);
  return calls;
}

test('new adaptations are draft PRs from the named fork; reruns reuse them', async () => {
  const [[operation, data]] = await scenario();
  assert.equal(operation, 'create');
  assert.equal(data.draft, true);
  assert.equal(data.head_repo, 'mathlib4-batteries-adaptations');
  assert.equal(data.head, 'leanprover-community:batteries-pr-testing-42');
  assert.equal(data.base, 'master');
  assert.deepEqual(await scenario({ prs: [pr] }), []);
});

test('merged sources publish dependency-only PRs as well as adaptations', async () => {
  assert.deepEqual(await scenario({ state: 'merged', prs: [pr] }), [['ready', { id: 'PR_100' }]]);
  const [[, data]] = await scenario({ state: 'merged' });
  assert.equal(data.draft, false);
  assert.deepEqual(await scenario({ state: 'merged', prs: [{ ...pr, draft: false }] }), []);
});

test('closed sources and empty updates close the adaptation PR', async () => {
  for (const options of [{ state: 'closed' }, { state: 'merged', changes: false }]) {
    assert.deepEqual(await scenario({ ...options, prs: [pr] }), [
      ['update', { owner: 'leanprover-community', repo: 'mathlib4', pull_number: 100, state: 'closed' }],
    ]);
    assert.deepEqual(await scenario(options), []);
    assert.deepEqual(await scenario({ ...options, prs: [{ ...pr, state: 'closed' }] }), []);
  }
});

test('open sources stay draft; closed Mathlib PRs remain closed, including Bors merges', async () => {
  assert.deepEqual(await scenario({ prs: [{ ...pr, draft: false }] }), [['draft', { id: 'PR_100' }]]);
  for (const state of ['open', 'merged', 'closed']) {
    assert.deepEqual(await scenario({ state, prs: [{ ...pr, state: 'closed', merged_at: null }] }), []);
  }
});

test('same-named branches in nightly-testing do not select the wrong PR', async () => {
  const old = { ...pr, head: { repo: { full_name: 'leanprover-community/mathlib4-nightly-testing' } } };
  assert.equal((await scenario({ prs: [old] }))[0][0], 'create');
});

test('late events do not change the PR state', async () => {
  assert.deepEqual(await scenario({ currentSHA: 'b'.repeat(40) }), []);
  assert.deepEqual(await scenario({ currentState: 'merged' }), []);
  assert.deepEqual(await scenario({ state: 'closed', currentState: 'open', prs: [pr] }), []);
});
