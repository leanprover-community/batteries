const crypto = require('node:crypto');
const fs = require('node:fs');
const os = require('node:os');
const path = require('node:path');
const { execFileSync } = require('node:child_process');

const remote = { owner: 'leanprover-community', repo: 'downstream-reports' };
const workflow = 'batteries-pr-validation.yml';
const sleep = ms => new Promise(resolve => setTimeout(resolve, ms));

function appJWT(id, key, now = Date.now()) {
  const encode = value => Buffer.from(JSON.stringify(value)).toString('base64url');
  const seconds = Math.floor(now / 1000);
  const unsigned = `${encode({ alg: 'RS256', typ: 'JWT' })}.` +
    encode({ iat: seconds - 30, exp: seconds + 540, iss: id });
  return `${unsigned}.${crypto.sign('RSA-SHA256', Buffer.from(unsigned), key).toString('base64url')}`;
}

function tokenProvider(github, core, now = Date.now) {
  let token;
  let expires = 0;
  return async () => {
    // App tokens expire after one hour. Queue waits can span several tokens.
    if (!token || now() >= expires - 5 * 60 * 1000) {
      const jwt = appJWT(process.env.APP_ID, process.env.APP_PRIVATE_KEY, now());
      core.setSecret(jwt);
      const headers = { authorization: `Bearer ${jwt}` };
      const { data: installation } = await github.request('GET /repos/{owner}/{repo}/installation', {
        ...remote, headers,
      });
      const { data } = await github.request('POST /app/installations/{installation_id}/access_tokens', {
        installation_id: installation.id, repositories: [remote.repo],
        permissions: { actions: 'write', contents: 'read' }, headers,
      });
      token = data.token;
      core.setSecret(token);
      expires = Date.parse(data.expires_at);
    }
    return { authorization: `Bearer ${token}` };
  };
}

async function waitForRun({ github, headers, requestId, created, core,
  timeout = 285 * 60 * 1000, pause = sleep, now = Date.now }) {
  const deadline = now() + timeout;
  let run;
  let previousState;
  while (now() < deadline) {
    if (!run) {
      const runs = await github.paginate(github.rest.actions.listWorkflowRuns, {
        ...remote, workflow_id: workflow, branch: 'main', event: 'workflow_dispatch',
        created: `>=${created}`, per_page: 100, headers: await headers(),
      });
      const matches = runs.filter(candidate => candidate.display_title === `batteries-pr-validation:${requestId}`);
      if (matches.length > 1) throw new Error('Multiple downstream runs have the same request ID');
      run = matches[0];
      if (run) core.info(`Downstream validation: ${run.html_url}`);
    }
    if (run) {
      ({ data: run } = await github.rest.actions.getWorkflowRun({
        ...remote, run_id: run.id, headers: await headers(),
      }));
      if (run.status !== previousState) {
        core.info(`Downstream run ${run.id}: ${run.status}`);
        previousState = run.status;
      }
      if (run.status === 'completed') {
        if (run.conclusion !== 'success') {
          throw new Error(`Downstream workflow ended with ${run.conclusion}; no adaptation PR is opened`);
        }
        return run;
      }
    }
    await pause(30000);
  }
  if (run) {
    await github.rest.actions.cancelWorkflowRun({ ...remote, run_id: run.id, headers: await headers() });
  }
  throw new Error('Timed out waiting for downstream validation; no adaptation PR is opened');
}

function buildResult(result, inputs) {
  for (const field of ['request_id', 'pr_number', 'batteries_repo', 'batteries_sha',
    'mathlib_sha', 'adaptation_fork', 'adaptation_pr']) {
    if (result[field] !== inputs[field]) throw new Error(`Downstream result does not match ${field}`);
  }
  const statuses = inputs.adaptation_pr ? { prepared: 'skipped' } : { pass: 'success', fail: 'failure' };
  if (!statuses[result.status]) {
    throw new Error(`Downstream validation returned ${result.status}; no adaptation PR is opened`);
  }
  return statuses[result.status];
}

async function readResult(github, headers, runId) {
  const artifacts = await github.paginate(github.rest.actions.listWorkflowRunArtifacts, {
    ...remote, run_id: runId, per_page: 100, headers: await headers(),
  });
  const matches = artifacts.filter(artifact => artifact.name === 'batteries-validation-result' && !artifact.expired);
  if (matches.length !== 1) throw new Error('The downstream result artifact is missing or ambiguous');
  const { data } = await github.rest.actions.downloadArtifact({
    ...remote, artifact_id: matches[0].id, archive_format: 'zip', headers: await headers(),
  });
  const directory = fs.mkdtempSync(path.join(os.tmpdir(), 'batteries-result-'));
  try {
    const archive = path.join(directory, 'result.zip');
    fs.writeFileSync(archive, Buffer.from(data));
    // Read one bounded JSON entry. Never execute or extract candidate files.
    return JSON.parse(execFileSync('unzip', ['-p', archive, 'result.json'], {
      encoding: 'utf8', maxBuffer: 1024 * 1024,
    }));
  } finally {
    fs.rmSync(directory, { recursive: true, force: true });
  }
}

async function dispatchAndWait({ github, context, core }) {
  const inputs = {
    request_id: `${context.runId}-${process.env.GITHUB_RUN_ATTEMPT || '1'}`,
    pr_number: process.env.PR_NUMBER, batteries_repo: process.env.BATTERIES_REPO,
    batteries_sha: process.env.BATTERIES_SHA, mathlib_sha: process.env.MATHLIB_SHA,
    adaptation_fork: process.env.ADAPTATION_FORK, adaptation_pr: process.env.ADAPTATION_PR || '',
  };
  const headers = tokenProvider(github, core);
  const created = new Date(Date.now() - 30000).toISOString();
  await github.rest.actions.createWorkflowDispatch({
    ...remote, workflow_id: workflow, ref: 'main', inputs, headers: await headers(),
  });
  const run = await waitForRun({ github, headers, requestId: inputs.request_id, created, core });
  const result = await readResult(github, headers, run.id);
  core.setOutput('build_result', buildResult(result, inputs));
  core.setOutput('downstream_run', run.id);
  core.setOutput('downstream_url', run.html_url);
}

module.exports = { appJWT, tokenProvider, waitForRun, buildResult, readResult, dispatchAndWait };
