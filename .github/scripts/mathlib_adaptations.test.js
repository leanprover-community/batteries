const { test } = require('node:test');
const assert = require('node:assert/strict');
const helpers = require('./mathlib_adaptations.js');

const sha = 'a'.repeat(40);
const mathlibSHA = 'b'.repeat(40);
const fork = 'mathlib4-adaptations';
const repo = { owner: 'leanprover-community', repo: 'batteries' };
const batteriesPR = {
  number: 123, state: 'open', base: { ref: 'main' },
  labels: [{ name: 'mathlib-adaptations' }],
  user: { login: 'contributor' },
  head: { sha, ref: 'change-batteries', repo: { full_name: 'contributor/batteries' } },
};
const adaptation = {
  number: 456, state: 'open', base: { ref: 'master' }, html_url: 'https://github.com/example/pr/456',
  head: { sha: mathlibSHA, ref: 'adaptations/batteries-123',
    repo: { full_name: `leanprover-community/${fork}` } },
};

function fixture(options = {}) {
  const calls = [];
  const outputs = {};
  const record = (method, result) => async args => {
    calls.push({ method, args });
    return { data: result };
  };
  const github = {
    rest: {
      repos: {
        listPullRequestsAssociatedWithCommit: 'associated',
        get: record('repo', { fork: true, parent: { full_name: 'leanprover-community/mathlib4' } }),
        getBranch: record('base', { commit: { sha: mathlibSHA } }),
        getCollaboratorPermissionLevel: record('permission', { permission: options.permission || 'write' }),
      },
      pulls: {
        list: 'pulls',
        get: async args => ({ data: args.repo === 'batteries' ?
          options.batteriesPR || batteriesPR : options.adaptation || adaptation }),
        create: record('createPR', adaptation),
      },
      issues: {
        listComments: 'comments',
        removeLabel: record('removeLabel', {}), addLabels: record('addLabels', {}),
        createComment: record('createComment', {}), updateComment: record('updateComment', {}),
        getLabel: record('getLabel', {}), createLabel: record('createLabel', {}),
        updateLabel: record('updateLabel', {}),
      },
      actions: { listWorkflowRuns: 'ci', createWorkflowDispatch: record('dispatch', {}) },
    },
    paginate: async method => ({
      associated: options.candidates || [batteriesPR],
      pulls: options.adaptations || [], comments: options.comments || [],
      ci: options.ci || [{ id: 1, head_sha: sha, head_repository: { full_name: 'contributor/batteries' },
        status: 'completed', conclusion: 'success' }],
    })[method],
  };
  return { github, calls, outputs,
    core: { setOutput: (key, value) => { outputs[key] = value; }, info: () => {} },
    context: { repo, runId: 789, payload: { workflow_run: { head_sha: sha } } },
  };
}

test.beforeEach(() => {
  process.env.ADAPTATION_FORK = fork;
  process.env.PR_NUMBER = '123';
  process.env.BATTERIES_SHA = sha;
  process.env.MATHLIB_SHA = mathlibSHA;
  process.env.BUILD_RESULT = 'success';
  process.env.ADAPTATION_URL = '';
});

test('the plan skips a stale successful CI run', async () => {
  const f = fixture({ candidates: [{ ...batteriesPR, head: { sha: 'c'.repeat(40) } }] });
  await helpers.plan(f);
  assert.deepEqual(f.outputs, {});
  assert.deepEqual(f.calls, []);
});

test('the plan skips closed PRs and other target branches', async () => {
  for (const pr of [{ ...batteriesPR, state: 'closed' },
    { ...batteriesPR, base: { ref: 'nightly-testing' } }]) {
    const f = fixture({ candidates: [pr] });
    await helpers.plan(f);
    assert.deepEqual(f.outputs, {});
  }
});

test('a fork with the same branch name cannot supply the adaptation PR', async () => {
  const other = { ...adaptation, head: { ...adaptation.head, repo: { full_name: 'leanprover-community/other' } } };
  const f = fixture({ adaptations: [other, adaptation] });
  await helpers.plan(f);
  assert.equal(f.outputs.adaptation_pr, 456);
  assert.equal(f.outputs.batteries_repo, 'contributor/batteries');
  assert.equal(f.outputs.mathlib_sha, mathlibSHA);
});

test('a new adaptation is a draft PR with an explicit same-owner head repository', async () => {
  const f = fixture();
  await helpers.openAdaptation(f);
  const request = f.calls.find(call => call.method === 'createPR').args;
  assert.equal(request.draft, true);
  assert.equal(request.head_repo, fork);
  assert.equal(request.head, 'leanprover-community:adaptations/batteries-123');
  assert.equal(f.outputs.adaptation_url, adaptation.html_url);
});

test('refreshing an adaptation does not create a second PR', async () => {
  const f = fixture({ adaptations: [adaptation] });
  await helpers.openAdaptation(f);
  assert.equal(f.calls.length, 0);
});

test('an initial success reports without an adaptation PR', async () => {
  const f = fixture();
  await helpers.reportInitial(f);
  assert.deepEqual(f.calls.find(call => call.method === 'addLabels').args.labels, ['builds-mathlib']);
  assert.match(f.calls.find(call => call.method === 'createComment').args.body, /No adaptation PR is needed/);
});

test('an updated adaptation clears the previous result while fork CI is pending', async () => {
  process.env.BUILD_RESULT = 'skipped';
  process.env.ADAPTATION_URL = adaptation.html_url;
  const f = fixture();
  await helpers.reportInitial(f);
  assert.equal(f.calls.filter(call => call.method === 'removeLabel').length, 2);
  assert.equal(f.calls.filter(call => call.method === 'addLabels').length, 0);
});

test('stale results do not change Batteries feedback', async () => {
  const f = fixture({ batteriesPR: { ...batteriesPR, head: { sha: 'c'.repeat(40) } } });
  await helpers.reportInitial(f);
  assert.equal(f.calls.length, 0);
});

const result = { batteries_pr_number: 123, batteries_sha: sha,
  mathlib_pr_number: 456, mathlib_sha: mathlibSHA, result: 'success' };

test('a callback ignores a newer Mathlib head and results from other forks', async () => {
  for (const head of [{ ...adaptation.head, sha: 'c'.repeat(40) },
    { ...adaptation.head, repo: { full_name: 'leanprover-community/other' } }]) {
    const f = fixture({ adaptation: { ...adaptation, head } });
    f.context.payload.client_payload = result;
    await helpers.reportAdaptation(f);
    assert.equal(f.calls.length, 0);
  }
});

test('a current callback updates the existing bot comment', async () => {
  const f = fixture({ comments: [{ id: 1, user: { login: 'github-actions[bot]' },
    body: '<!-- mathlib-adaptation-status -->\nold result' }] });
  f.context.payload.client_payload = result;
  await helpers.reportAdaptation(f);
  assert.equal(f.calls.filter(call => call.method === 'createComment').length, 0);
  assert.equal(f.calls.find(call => call.method === 'updateComment').args.comment_id, 1);
});

test('unsafe fork names and malformed results are rejected', () => {
  for (const name of ['', 'mathlib4', 'mathlib4-nightly-testing', 'owner/repo', '--bad/name']) {
    assert.throws(() => helpers.forkName(name));
  }
  for (const change of [{ result: 'cancelled' }, { batteries_pr_number: '123' }, { mathlib_sha: 'HEAD' }]) {
    assert.equal(helpers.validResult({ ...result, ...change }), false);
  }
});

test('a passing CI run does not dispatch an unrequested PR', async () => {
  const f = fixture({ batteriesPR: { ...batteriesPR, labels: [] } });
  await helpers.plan(f);
  assert.deepEqual(f.outputs, {});
  assert.deepEqual(f.calls, []);
});

test('a repeated CI event skips an already completed validation for both SHAs', async () => {
  const f = fixture({ comments: [{ user: { login: 'github-actions[bot]' },
    body: `<!-- mathlib-adaptation-status -->\n<!-- mathlib-validation:${sha}:${mathlibSHA} -->` }] });
  await helpers.plan(f);
  assert.deepEqual(f.outputs, {});
});

test('only a standalone adaptations directive requests a build', async () => {
  assert.equal(helpers.command('Please run !adaptations'), false);
  assert.equal(helpers.command('Context\n  !adaptations\r\n'), true);
  const f = fixture();
  f.context.payload = { issue: { number: 123 }, comment: { body: 'Please run !adaptations' } };
  await helpers.requestAdaptations(f);
  assert.deepEqual(f.calls, []);
});

test('a request after CI passes opts in and dispatches the current fork branch', async () => {
  const f = fixture();
  f.context.payload = { issue: { number: 123 }, comment: { body: '!adaptations', user: { login: 'maintainer' } } };
  await helpers.requestAdaptations(f);
  assert.deepEqual(f.calls.find(call => call.method === 'dispatch').args.inputs,
    { pr_number: '123', head_repo: 'contributor/batteries', head_branch: 'change-batteries' });
  assert.deepEqual(f.calls.find(call => call.method === 'addLabels').args.labels,
    ['mathlib-adaptations', 'mathlib-not-checked']);
});

test('a request during CI records the opt-in without a premature dispatch', async () => {
  const f = fixture({ ci: [{ id: 1, head_sha: sha, head_repository: { full_name: 'contributor/batteries' },
    status: 'in_progress', conclusion: null }] });
  f.context.payload = { issue: { number: 123 }, comment: { body: '!adaptations', user: { login: 'maintainer' } } };
  await helpers.requestAdaptations(f);
  assert.equal(f.calls.filter(call => call.method === 'addLabels').length, 1);
  assert.equal(f.calls.filter(call => call.method === 'dispatch').length, 0);
});

test('unrelated read-only commenters cannot opt a PR into expensive builds', async () => {
  const f = fixture({ permission: 'read' });
  f.context.payload = { issue: { number: 123 }, comment: { body: '!adaptations', user: { login: 'outsider' } } };
  await helpers.requestAdaptations(f);
  assert.deepEqual(f.calls.map(call => call.method), ['permission']);
});

test('a new PR revision receives the unchecked label and clears old verdicts', async () => {
  const f = fixture();
  f.context.payload = { action: 'synchronize', pull_request: batteriesPR };
  await helpers.requestAdaptations(f);
  assert.deepEqual(f.calls.find(call => call.method === 'addLabels').args.labels, ['mathlib-not-checked']);
  assert.equal(f.calls.filter(call => call.method === 'removeLabel').length, 2);
  assert.equal(f.calls.filter(call => call.method === 'dispatch').length, 0);
});

test('a delayed push event cannot replace a completed result with unchecked', async () => {
  const f = fixture({ comments: [{ user: { login: 'github-actions[bot]' },
    body: `<!-- mathlib-adaptation-status -->\n<!-- mathlib-checked:${sha} -->` }] });
  f.context.payload = { action: 'synchronize', pull_request: batteriesPR };
  await helpers.requestAdaptations(f);
  assert.equal(f.calls.filter(call => call.method === 'addLabels').length, 0);
});

test('removing the opt-in stops publication of an in-flight result', async () => {
  const f = fixture({ batteriesPR: { ...batteriesPR, labels: [] } });
  await helpers.reportInitial(f);
  assert.deepEqual(f.calls, []);
});

test('completed validation removes the unchecked label', async () => {
  const f = fixture();
  await helpers.reportInitial(f);
  assert.ok(f.calls.some(call => call.method === 'removeLabel' && call.args.name === 'mathlib-not-checked'));
});

test('PR authors can request adaptations without repository write access', async () => {
  const f = fixture({ permission: 'read' });
  f.context.payload = { issue: { number: 123 }, comment: { body: '!adaptations', user: { login: 'contributor' } } };
  await helpers.requestAdaptations(f);
  assert.ok(f.calls.some(call => call.method === 'dispatch'));
});

test('a direct opt-in label requests the current PR build', async () => {
  const f = fixture();
  f.context.actor = 'maintainer';
  f.context.payload = { action: 'labeled', pull_request: batteriesPR };
  await helpers.requestAdaptations(f);
  assert.ok(f.calls.some(call => call.method === 'dispatch'));
});

test('manual requests revalidate CI and keep the same branch concurrency key', async () => {
  const f = fixture();
  f.context.payload = { inputs: { pr_number: '123', head_repo: 'contributor/batteries', head_branch: 'change-batteries' } };
  await helpers.plan(f);
  assert.equal(f.outputs.batteries_sha, sha);
  const pending = fixture({ ci: [] });
  pending.context.payload = f.context.payload;
  await helpers.plan(pending);
  assert.deepEqual(pending.outputs, {});
});

test('the unchecked label tooltip advertises the adaptations command', async () => {
  const f = fixture();
  f.github.rest.issues.getLabel = async () => { throw { status: 404 }; };
  await helpers.ensureLabels(f.github, repo);
  const label = f.calls.find(call => call.method === 'createLabel' && call.args.name === 'mathlib-not-checked');
  assert.equal(label.args.description,
    'Mathlib has not been checked for this revision. Comment !adaptations to request a check.');
  assert.ok(label.args.description.length <= 100);
});
