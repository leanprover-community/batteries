const owner = 'leanprover-community';
const mathlib = { owner, repo: 'mathlib4' };

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
  // Read the current PR. A previous successful CI run must not test a new head.
  const candidates = await github.paginate(github.rest.repos.listPullRequestsAssociatedWithCommit, {
    ...context.repo, commit_sha: run.head_sha, per_page: 100,
  });
  const current = candidates.filter(pr => isCurrentPR(pr, run.head_sha));
  if (current.length !== 1) {
    core.info('No unique, current Batteries PR targeting main; skip this run');
    return;
  }
  const pr = current[0];
  const fork = forkName(process.env.ADAPTATION_FORK);
  const { data: repository } = await github.rest.repos.get({ owner, repo: fork });
  if (!repository.fork || repository.parent?.full_name !== `${owner}/mathlib4`) {
    throw new Error('The adaptation repository must be a fork of Mathlib');
  }
  const { data: base } = await github.rest.repos.getBranch({ ...mathlib, branch: 'master' });
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
  return isCurrentPR(pr, process.env.BATTERIES_SHA);
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
  const marker = '<!-- mathlib-adaptation-status -->';
  const comments = await github.paginate(github.rest.issues.listComments, { ...issue, per_page: 100 });
  const previous = comments.find(comment => comment.user.login === 'github-actions[bot]' && comment.body?.includes(marker));
  const body = `${marker}\n${message}`;
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
  const url = `https://github.com/${context.repo.owner}/${context.repo.repo}/actions/runs/${context.runId}`;
  const message = [
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
  if (!isCurrentPR(batteriesPR, result.batteries_sha)) return;
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
    `Mathlib CI ${result.result === 'success' ? 'passes' : 'fails'} for Batteries ` +
    `\`${result.batteries_sha}\` and Mathlib \`${result.mathlib_sha}\`.\n\n` +
    `Adaptation PR: ${mathlibPR.html_url}`);
}

module.exports = {
  forkName, isCurrentPR, findAdaptation, plan, isCurrent, openAdaptation,
  updateFeedback, reportInitial, validResult, reportAdaptation,
};
