const owner = 'leanprover-community';
const mathlib = { owner, repo: 'mathlib4' };
const REQUESTED = 'mathlib-adaptations';
const NOT_CHECKED = 'mathlib-not-checked';

function requested(pr) {
  return pr.labels?.some(label => label.name === REQUESTED);
}

function command(body) {
  return (body || '').split(/\r?\n/).some(line => line.trim() === '!adaptations');
}

async function statusComment(github, repo, number) {
  const comments = await github.paginate(github.rest.issues.listComments, {
    ...repo, issue_number: number, per_page: 100,
  });
  return comments.find(comment => comment.user.login === 'github-actions[bot]' &&
    comment.body?.includes('<!-- mathlib-adaptation-status -->'));
}

async function passingCI(github, repo, pr) {
  const runs = await github.paginate(github.rest.actions.listWorkflowRuns, {
    ...repo, workflow_id: 'build.yml', event: 'pull_request', head_sha: pr.head.sha, per_page: 100,
  });
  const latest = runs.filter(run => run.head_sha === pr.head.sha &&
    run.head_repository?.full_name === pr.head.repo.full_name).sort((a, b) => b.id - a.id)[0];
  return latest?.status === 'completed' && latest.conclusion === 'success';
}

async function ensureLabels(github, repo) {
  for (const label of [
    { name: NOT_CHECKED, color: 'fbca04', description: 'Mathlib has not been checked for this revision. Comment !adaptations to request a check.' },
    { name: REQUESTED, color: 'c5def5', description: 'Opt in to Mathlib validation and automatic adaptation updates after Batteries CI passes.' },
  ]) {
    try {
      const { data } = await github.rest.issues.getLabel({ ...repo, name: label.name });
      if (data.description !== label.description) {
        await github.rest.issues.updateLabel({ ...repo, name: label.name, description: label.description });
      }
    } catch (error) {
      if (error.status !== 404) throw error;
      try {
        await github.rest.issues.createLabel({ ...repo, ...label });
      } catch (creationError) {
        if (creationError.status !== 422) throw creationError;
        // Another PR may initialize the same repository label concurrently.
        await github.rest.issues.getLabel({ ...repo, name: label.name });
      }
    }
  }
}

async function requestAdaptations({ github, context, core }) {
  const comment = context.payload.comment;
  if (comment && !command(comment.body)) return;
  const number = context.payload.issue?.number || context.payload.pull_request.number;
  const { data: pr } = await github.rest.pulls.get({ ...context.repo, pull_number: number });
  if (pr.state !== 'open' || pr.base.ref !== 'main') return;
  const issue = { ...context.repo, issue_number: number };
  if (comment || context.payload.action === 'labeled') {
    const { data: access } = await github.rest.repos.getCollaboratorPermissionLevel({
      ...context.repo, username: comment?.user.login || context.actor,
    });
    const roles = ['triage', 'write', 'maintain', 'admin'];
    if (comment?.user.login !== pr.user?.login &&
        !roles.includes(access.permission) && !roles.includes(access.role_name)) {
      core.info('Mathlib adaptation requests require PR authorship, triage access, or write access');
      return;
    }
  }
  await ensureLabels(github, context.repo);
  if (!comment && context.payload.action !== 'labeled') {
    // A delayed event must not clear a result already posted for this head.
    if (pr.head.sha !== context.payload.pull_request.head.sha) return;
    const previous = await statusComment(github, context.repo, number);
    if (previous?.body.includes(`<!-- mathlib-checked:${pr.head.sha} -->`)) return;
    await github.rest.issues.addLabels({ ...issue, labels: [NOT_CHECKED] });
    for (const name of ['builds-mathlib', 'breaks-mathlib']) {
      try { await github.rest.issues.removeLabel({ ...issue, name }); }
      catch (error) { if (error.status !== 404) throw error; }
    }
    return;
  }
  await github.rest.issues.addLabels({ ...issue, labels: [REQUESTED, NOT_CHECKED] });
  for (const name of ['builds-mathlib', 'breaks-mathlib']) {
    try { await github.rest.issues.removeLabel({ ...issue, name }); }
    catch (error) { if (error.status !== 404) throw error; }
  }
  if (!await passingCI(github, context.repo, pr)) {
    core.info('Request recorded; wait for successful Batteries CI at the current head');
    return;
  }
  // workflow_dispatch is one of the events that GITHUB_TOKEN can trigger.
  await github.rest.actions.createWorkflowDispatch({
    ...context.repo, workflow_id: 'test_mathlib.yml', ref: 'main', inputs: {
      pr_number: String(number), head_repo: pr.head.repo.full_name, head_branch: pr.head.ref,
    },
  });
}

function forkName(name) {
  if (!/^[A-Za-z0-9_.-]+$/.test(name || '') ||
      ['mathlib4', 'mathlib4-nightly-testing'].includes(name)) {
    throw new Error('Set MATHLIB_ADAPTATION_FORK to a dedicated Mathlib fork name');
  }
  return name;
}

function isCurrentPR(pr, sha) {
  return pr.state === 'open' && pr.base.ref === 'main' && pr.head.sha === sha;
}

async function findAdaptation(github, number, fork) {
  const prs = await github.paginate(github.rest.pulls.list, {
    ...mathlib, state: 'open', base: 'master',
    head: `${owner}:adaptations/batteries-${number}`, per_page: 100,
  });
  return prs.find(pr => pr.head.repo?.full_name === `${owner}/${fork}`);
}

async function plan({ github, context, core }) {
  const run = context.payload.workflow_run;
  let pr;
  if (run) {
    const candidates = await github.paginate(github.rest.repos.listPullRequestsAssociatedWithCommit, {
      ...context.repo, commit_sha: run.head_sha, per_page: 100,
    });
    const current = candidates.filter(pr => isCurrentPR(pr, run.head_sha));
    if (current.length !== 1) {
      core.info('No unique, current Batteries PR targeting main; skip this run');
      return;
    }
    // Fetch live labels so a label removal disables subsequent work.
    ({ data: pr } = await github.rest.pulls.get({ ...context.repo, pull_number: current[0].number }));
    if (!isCurrentPR(pr, run.head_sha)) return;
  } else {
    const input = context.payload.inputs;
    if (!/^[1-9][0-9]*$/.test(input.pr_number)) throw new Error('Invalid PR number');
    ({ data: pr } = await github.rest.pulls.get({ ...context.repo, pull_number: Number(input.pr_number) }));
    if (pr.state !== 'open' || pr.base.ref !== 'main' ||
        pr.head.repo.full_name !== input.head_repo || pr.head.ref !== input.head_branch ||
        !await passingCI(github, context.repo, pr)) return;
  }
  if (!requested(pr)) {
    core.info('Mathlib adaptations were not requested; skip this PR');
    return;
  }
  const fork = forkName(process.env.ADAPTATION_FORK);
  const { data: repository } = await github.rest.repos.get({ owner, repo: fork });
  if (!repository.fork || repository.parent?.full_name !== `${owner}/mathlib4`) {
    throw new Error('The adaptation repository must be a fork of Mathlib');
  }
  const { data: base } = await github.rest.repos.getBranch({ ...mathlib, branch: 'master' });
  if (run) {
    const previous = await statusComment(github, context.repo, pr.number);
    if (previous?.body.includes(`<!-- mathlib-validation:${pr.head.sha}:${base.commit.sha} -->`)) return;
  }
  const adaptation = await findAdaptation(github, pr.number, fork);
  for (const [key, value] of Object.entries({
    pr_number: pr.number, batteries_sha: pr.head.sha,
    batteries_repo: pr.head.repo.full_name, mathlib_sha: base.commit.sha,
    adaptation_fork: fork, adaptation_pr: adaptation?.number || '',
  })) core.setOutput(key, value);
}

async function isCurrent({ github, context }) {
  const { data: pr } = await github.rest.pulls.get({
    ...context.repo, pull_number: Number(process.env.PR_NUMBER),
  });
  return isCurrentPR(pr, process.env.BATTERIES_SHA) && requested(pr);
}

async function openAdaptation({ github, core }) {
  const number = Number(process.env.PR_NUMBER);
  const fork = forkName(process.env.ADAPTATION_FORK);
  let pr = await findAdaptation(github, number, fork);
  if (!pr) {
    ({ data: pr } = await github.rest.pulls.create({
      ...mathlib, base: 'master', head: `${owner}:adaptations/batteries-${number}`,
      head_repo: fork, draft: true,
      title: `chore: adapt to Batteries PR #${number}`,
      body: [
        `The initial Mathlib build fails with leanprover-community/batteries#${number}.`,
        'This draft contains the dependency update. Add the required Mathlib adaptations here.',
        '',
        'The bot refreshes the dependency when Batteries CI succeeds. It preserves adaptation commits.',
        'After the Batteries PR merges, restore the dependency to Batteries main and update the manifest.',
        'Then close this PR if no adaptations remain, or request Mathlib review.',
        '',
        `<!-- batteries-adaptation:${number} -->`,
      ].join('\n'),
    }));
  }
  core.setOutput('adaptation_url', pr.html_url);
}

async function updateFeedback(github, repo, number, label, message) {
  const issue = { ...repo, issue_number: number };
  for (const name of ['builds-mathlib', 'breaks-mathlib']) {
    if (name === label) continue;
    try {
      await github.rest.issues.removeLabel({ ...issue, name });
    } catch (error) {
      if (error.status !== 404) throw error;
    }
  }
  if (label) await github.rest.issues.addLabels({ ...issue, labels: [label] });
  if (label) {
    try { await github.rest.issues.removeLabel({ ...issue, name: NOT_CHECKED }); }
    catch (error) { if (error.status !== 404) throw error; }
  }
  const marker = '<!-- mathlib-adaptation-status -->';
  const comments = await github.paginate(github.rest.issues.listComments, { ...issue, per_page: 100 });
  const previous = comments.find(comment => comment.user.login === 'github-actions[bot]' && comment.body?.includes(marker));
  const validation = previous?.body.match(/<!-- mathlib-validation:[a-f0-9]{40}:[a-f0-9]{40} -->/)?.[0];
  const body = `${marker}\n${message}` +
    (validation && !message.includes('<!-- mathlib-validation:') ? `\n${validation}` : '');
  if (previous) {
    if (previous.body !== body) {
      await github.rest.issues.updateComment({ ...repo, comment_id: previous.id, body });
    }
  } else {
    await github.rest.issues.createComment({ ...issue, body });
  }
}

async function reportInitial({ github, context }) {
  if (!await isCurrent({ github, context })) return;
  const success = process.env.BUILD_RESULT === 'success';
  const failed = process.env.BUILD_RESULT === 'failure';
  const label = success ? 'builds-mathlib' : failed ? 'breaks-mathlib' : null;
  const url = process.env.DOWNSTREAM_URL ||
    `https://github.com/${context.repo.owner}/${context.repo.repo}/actions/runs/${context.runId}`;
  const message = [
    `<!-- mathlib-validation:${process.env.BATTERIES_SHA}:${process.env.MATHLIB_SHA} -->`,
    success || failed ? `<!-- mathlib-checked:${process.env.BATTERIES_SHA} -->` : '',
    `Mathlib validation for Batteries \`${process.env.BATTERIES_SHA}\`:`,
    success ? 'The initial build passes. No adaptation PR is needed.' :
      failed ? 'The initial build fails. The draft adaptation PR is ready for fixes.' :
        'The adaptation branch is updated. Ordinary Mathlib CI is pending.',
    process.env.ADAPTATION_URL ? `Adaptation PR: ${process.env.ADAPTATION_URL}` : '',
    `Validation run: ${url}`,
  ].filter(Boolean).join('\n\n');
  await updateFeedback(github, context.repo, Number(process.env.PR_NUMBER), label, message);
}

function validResult(result) {
  return ['success', 'failure'].includes(result.result) &&
    Number.isSafeInteger(result.batteries_pr_number) && result.batteries_pr_number > 0 &&
    Number.isSafeInteger(result.mathlib_pr_number) && result.mathlib_pr_number > 0 &&
    /^[a-f0-9]{40}$/.test(result.batteries_sha || '') &&
    /^[a-f0-9]{40}$/.test(result.mathlib_sha || '');
}

async function reportAdaptation({ github, context }) {
  const result = context.payload.client_payload;
  if (!validResult(result)) throw new Error('Invalid Mathlib adaptation result');
  const { data: batteriesPR } = await github.rest.pulls.get({
    ...context.repo, pull_number: result.batteries_pr_number,
  });
  if (!isCurrentPR(batteriesPR, result.batteries_sha) || !requested(batteriesPR)) return;
  const { data: mathlibPR } = await github.rest.pulls.get({
    ...mathlib, pull_number: result.mathlib_pr_number,
  });
  const fork = forkName(process.env.ADAPTATION_FORK);
  if (mathlibPR.state !== 'open' || mathlibPR.base.ref !== 'master' ||
      mathlibPR.head.repo?.full_name !== `${owner}/${fork}` ||
      mathlibPR.head.ref !== `adaptations/batteries-${result.batteries_pr_number}` ||
      mathlibPR.head.sha !== result.mathlib_sha) return;
  const label = result.result === 'success' ? 'builds-mathlib' : 'breaks-mathlib';
  await updateFeedback(github, context.repo, result.batteries_pr_number, label,
    `<!-- mathlib-checked:${result.batteries_sha} -->\n` +
    `Mathlib CI ${result.result === 'success' ? 'passes' : 'fails'} for Batteries ` +
    `\`${result.batteries_sha}\` and Mathlib \`${result.mathlib_sha}\`.\n\n` +
    `Adaptation PR: ${mathlibPR.html_url}`);
}

module.exports = {
  requested, command, passingCI, ensureLabels, requestAdaptations,
  forkName, isCurrentPR, findAdaptation, plan, isCurrent, openAdaptation,
  updateFeedback, reportInitial, validResult, reportAdaptation,
};
