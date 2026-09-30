const { test } = require('node:test');
const assert = require('node:assert/strict');
const crypto = require('node:crypto');
const { execFileSync } = require('node:child_process');
const helpers = require('./dispatch_mathlib.js');

function queueFixture(states, discoverAfter = 1) {
  let clock = 0;
  let discoveries = 0;
  const readRuns = [];
  const cancelled = [];
  const run = { id: 42, display_title: 'batteries-pr-validation:123-1', html_url: 'https://github.com/example/run/42' };
  return {
    github: {
      paginate: async () => ++discoveries < discoverAfter ?
        [{ ...run, id: 99, display_title: 'batteries-pr-validation:other' }] : [run],
      rest: { actions: {
        listWorkflowRuns: 'list',
        getWorkflowRun: async args => {
          readRuns.push(args.run_id);
          return { data: { ...run, ...states[Math.min(readRuns.length - 1, states.length - 1)] } };
        },
        cancelWorkflowRun: async args => { cancelled.push(args.run_id); },
      } },
    },
    headers: async () => ({ authorization: 'Bearer test-token' }),
    core: { info: () => {} }, requestId: '123-1', created: '2026-09-30T00:00:00Z',
    now: () => clock, pause: async ms => { clock += ms; },
    readRuns, cancelled,
  };
}

test('the waiter discovers its request and waits through queue and execution states', async () => {
  const f = queueFixture([
    { status: 'queued' }, { status: 'in_progress' }, { status: 'completed', conclusion: 'success' },
  ], 2);
  const run = await helpers.waitForRun(f);
  assert.equal(run.id, 42);
  assert.deepEqual(f.readRuns, [42, 42, 42]);
  assert.deepEqual(f.cancelled, []);
});

test('cancelled and failed remote workflows cannot produce adaptation results', async () => {
  for (const conclusion of ['cancelled', 'failure', 'timed_out']) {
    await assert.rejects(helpers.waitForRun(queueFixture([{ status: 'completed', conclusion }])),
      /no adaptation PR is opened/);
  }
});

test('a queue timeout cancels the identified remote run', async () => {
  const f = queueFixture([{ status: 'queued' }]);
  await assert.rejects(helpers.waitForRun({ ...f, timeout: 45000 }), /Timed out/);
  assert.deepEqual(f.cancelled, [42]);
});

test('an ambiguous request ID is rejected', async () => {
  const f = queueFixture([]);
  f.github.paginate = async () => [1, 2].map(id => ({ id, display_title: 'batteries-pr-validation:123-1' }));
  await assert.rejects(helpers.waitForRun(f), /Multiple downstream runs/);
});

const inputs = {
  request_id: '123-1', pr_number: '42', batteries_repo: 'contributor/batteries',
  batteries_sha: 'a'.repeat(40), mathlib_sha: 'b'.repeat(40),
  adaptation_fork: 'mathlib4-adaptations', adaptation_pr: '',
};

test('only a matching compilation failure opens the failure path', () => {
  assert.equal(helpers.buildResult({ ...inputs, status: 'pass' }, inputs), 'success');
  assert.equal(helpers.buildResult({ ...inputs, status: 'fail' }, inputs), 'failure');
  for (const field of ['request_id', 'batteries_sha', 'mathlib_sha', 'adaptation_fork', 'pr_number']) {
    assert.throws(() => helpers.buildResult({ ...inputs, [field]: 'other', status: 'fail' }, inputs),
      /does not match/);
  }
  assert.throws(() => helpers.buildResult({ ...inputs, status: 'infra_failure' }, inputs),
    /no adaptation PR is opened/);
});

test('existing adaptations require a prepared result rather than a new initial build', () => {
  const existing = { ...inputs, adaptation_pr: '456' };
  assert.equal(helpers.buildResult({ ...existing, status: 'prepared' }, existing), 'skipped');
  assert.throws(() => helpers.buildResult({ ...existing, status: 'fail' }, existing));
});

test('App authentication is signed correctly and renewed during a long wait', async () => {
  const { privateKey, publicKey } = crypto.generateKeyPairSync('rsa', { modulusLength: 2048 });
  process.env.APP_ID = '123';
  process.env.APP_PRIVATE_KEY = privateKey.export({ type: 'pkcs8', format: 'pem' });
  let clock = 100000000;
  let minted = 0;
  const core = { setSecret: () => {} };
  const github = { request: async (route, args) => {
    const jwt = args.headers.authorization.slice(7).split('.');
    assert.equal(crypto.verify('RSA-SHA256', Buffer.from(jwt.slice(0, 2).join('.')),
      publicKey, Buffer.from(jwt[2], 'base64url')), true);
    if (route.startsWith('GET')) return { data: { id: 1 } };
    assert.deepEqual(args.repositories, ['downstream-reports']);
    assert.deepEqual(args.permissions, { actions: 'write', contents: 'read' });
    return { data: { token: `token-${++minted}`, expires_at: new Date(clock + 3600000).toISOString() } };
  } };
  const headers = helpers.tokenProvider(github, core, () => clock);
  assert.equal((await headers()).authorization, 'Bearer token-1');
  assert.equal((await headers()).authorization, 'Bearer token-1');
  clock += 3300001;
  assert.equal((await headers()).authorization, 'Bearer token-2');
});

test('the waiter reads bounded JSON from the selected run artifact', async () => {
  const archive = execFileSync('python3', ['-c',
    'import io,zipfile,sys; b=io.BytesIO(); z=zipfile.ZipFile(b,"w"); ' +
    'z.writestr("result.json",\'{"status":"pass"}\'); z.close(); sys.stdout.buffer.write(b.getvalue())']);
  const github = {
    paginate: async (_method, args) => {
      assert.equal(args.run_id, 42);
      return [{ id: 7, name: 'batteries-validation-result', expired: false }];
    },
    rest: { actions: {
      listWorkflowRunArtifacts: 'list',
      downloadArtifact: async args => {
        assert.equal(args.artifact_id, 7);
        return { data: archive };
      },
    } },
  };
  assert.deepEqual(await helpers.readResult(github, async () => ({}), 42), { status: 'pass' });
});
