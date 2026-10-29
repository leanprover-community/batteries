"""Run with Python, PyYAML, Node, Git, and jq. All GitHub writes are mocked."""

import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

import yaml


ROOT = Path(__file__).resolve().parents[2]
WORKFLOW = yaml.safe_load((ROOT / ".github/workflows/test_mathlib.yml").read_text())
SHA = "a" * 40
MAIN_REQUIRE = 'require "leanprover-community" / "batteries" @ git "main"\n'


def step(job, name):
    return next(s for s in WORKFLOW["jobs"][job]["steps"] if s.get("name") == name)


class WorkflowTests(unittest.TestCase):
    def setUp(self):
        temporary = tempfile.TemporaryDirectory()
        self.addCleanup(temporary.cleanup)
        self.root = Path(temporary.name)
        self.repo = self.root / "checkout"
        self.repo.mkdir()
        self.bin = self.root / "bin"
        self.bin.mkdir()
        self.output = self.root / "output"
        self.response = self.root / "response.json"
        self.env = {
            **os.environ, "PATH": f"{self.bin}:{os.environ['PATH']}",
            "GIT_CONFIG_GLOBAL": os.devnull, "GIT_CONFIG_NOSYSTEM": "1",
            "GIT_CONFIG_COUNT": "1",
            "GIT_CONFIG_KEY_0": f"url.{self.root}/.insteadOf",
            "GIT_CONFIG_VALUE_0": "https://github.com/leanprover-community/",
            "GITHUB_OUTPUT": str(self.output), "GH_RESPONSE": str(self.response),
            "GH_REPO": "leanprover-community/batteries", "GITHUB_EVENT_NAME": "workflow_run",
            "PR_NUMBER": "42", "PR_STATE": "open", "SHA": SHA, "BATTERIES_SHA": SHA,
            "HEAD_REPO": "contributor/batteries", "HEAD_BRANCH": "change",
            "BRANCH_SHA": "", "GH_TOKEN": "test", "READ_TOKEN": "test-read",
        }
        gh = self.bin / "gh"
        gh.write_text(f"#!{sys.executable}\n" + '''
import os, subprocess, sys
args = sys.argv[1:]
if args[:2] == ['auth', 'setup-git']:
    sys.exit(0)
response = open(os.environ['GH_RESPONSE']).read()
if args[:2] == ['pr', 'list']:
    result = subprocess.run(['jq', '-r', args[args.index('--jq') + 1]], input=response, text=True)
    sys.exit(result.returncode)
if args[0] == 'api':
    print(response)
else:
    raise RuntimeError(args)
''')
        gh.chmod(0o755)
        if sys.platform == "darwin":
            sed = self.bin / "sed"
            sed.write_text('#!/bin/sh\nshift\nexec /usr/bin/sed -i "" "$@"\n')
            sed.chmod(0o755)
        self.git("init", "-b", "master")
        self.git("config", "user.name", "Test")
        self.git("config", "user.email", "test@example.com")
        (self.repo / "lakefile.lean").write_text(MAIN_REQUIRE)
        self.package = {"name": "batteries", "type": "git", "rev": "b" * 40,
                        "url": "https://github.com/leanprover-community/batteries", "inputRev": "main"}
        (self.repo / "lake-manifest.json").write_text(json.dumps({"packages": [self.package]}))
        self.git("add", ".")
        self.git("commit", "-m", "base")
        self.env["MATHLIB_SHA"] = self.git("rev-parse", "HEAD").stdout.strip()
        self.git("clone", "--bare", str(self.repo), str(self.root / "mathlib4-batteries-adaptations.git"))
        self.source()

    def command(self, *args, check=True):
        result = subprocess.run(args, cwd=self.repo, env=self.env, capture_output=True, text=True)
        if check and result.returncode:
            self.fail(f"{args}:\n{result.stdout}\n{result.stderr}")
        return result

    def git(self, *args, **kwargs):
        return self.command("git", *args, **kwargs)

    def run_step(self, job, name, check=True):
        self.output.write_text("")
        return self.command("bash", "-c", step(job, name)["run"], check=check)

    def source(self, state="open", merged=False, sha=SHA):
        self.response.write_text(json.dumps({"state": state, "merged": merged,
                                             "base": {"ref": "main"}, "head": {"sha": sha}}))

    def cut(self):
        self.run_step("prepare", "Cut the testing branch")

    def publish(self, check=True):
        return self.run_step("push", "Commit and push", check=check)

    def test_find_only_the_current_pr_head(self):
        candidate = {"number": 42, "baseRefName": "main", "headRefName": "change",
                     "headRefOid": SHA, "headRepositoryOwner": {"login": "contributor"},
                     "headRepository": {"name": "batteries"}}
        for sha, expected in [(SHA, "number=42\nstate=open\n"), ("b" * 40, "")]:
            self.response.write_text(json.dumps([{**candidate, "headRefOid": sha}]))
            self.run_step("pr-info", "Find the PR")
            self.assertEqual(self.output.read_text(), expected)

    def test_close_event_reads_current_state(self):
        self.env["GITHUB_EVENT_NAME"] = "pull_request_target"
        for state, merged, expected in [("closed", True, "merged"), ("closed", False, "closed"),
                                         ("open", False, None)]:
            self.source(state, merged)
            self.run_step("pr-info", "Find the PR")
            if expected:
                self.assertIn(f"state={expected}", self.output.read_text())
            else:
                self.assertEqual(self.output.read_text(), "")

    def test_updates_preserve_adaptations_and_restore_main(self):
        self.cut()
        self.assertIn(SHA, (self.repo / "lakefile.lean").read_text())
        self.publish()
        (self.repo / "Adaptation.lean").write_text("-- contributor's fix\n")
        self.git("add", "Adaptation.lean")
        self.git("commit", "-m", "adapt Mathlib")
        self.git("push", "adaptations", "batteries-pr-testing-42")
        self.env["BRANCH_SHA"] = self.git("rev-parse", "HEAD").stdout.strip()
        self.git("switch", "master")
        self.git("branch", "-D", "batteries-pr-testing-42")
        self.git("remote", "remove", "adaptations")
        self.env["PR_STATE"] = "merged"
        self.source("closed", True)
        self.cut()
        self.assertEqual((self.repo / "lakefile.lean").read_text(), MAIN_REQUIRE)
        self.assertTrue((self.repo / "Adaptation.lean").exists())
        self.publish()
        self.assertIn("has_changes=true", self.output.read_text())
        self.assertEqual(self.git("merge-base", "--is-ancestor", self.env["BRANCH_SHA"], "HEAD").returncode, 0)

    def test_no_remaining_diff(self):
        self.env["PR_STATE"] = "merged"
        self.source("closed", True)
        self.cut()
        self.publish()
        self.assertIn("has_changes=false", self.output.read_text())

    def test_superseded_or_closed_source_is_not_pushed(self):
        self.cut()
        for state, merged, sha in [("open", False, "b" * 40), ("closed", False, SHA), ("closed", True, SHA)]:
            self.source(state, merged, sha)
            self.publish()
            self.assertEqual(self.output.read_text(), "")
        refs = self.git("ls-remote", "adaptations", "refs/heads/batteries-pr-testing-42").stdout
        self.assertEqual(refs, "")

    def test_concurrent_contributor_push_is_not_overwritten(self):
        self.cut()
        contributor = self.git("commit-tree", "HEAD^{tree}", "-p", "HEAD", "-m", "contributor fix").stdout.strip()
        self.git("push", "adaptations", f"{contributor}:refs/heads/batteries-pr-testing-42")
        self.assertNotEqual(self.publish(check=False).returncode, 0)
        self.assertIn(contributor, self.git("ls-remote", "adaptations", "refs/heads/batteries-pr-testing-42").stdout)

    def test_manifest_checks_dependency_and_accepts_new_dependencies(self):
        artifact = self.root / "manifest.json"
        self.env["RESULT"] = str(artifact)
        pinned = {**self.package, "url": "https://github.com/contributor/batteries", "rev": SHA, "inputRev": SHA}
        for state, package, valid in [("open", pinned, True), ("open", self.package, False),
                                       ("merged", self.package, True), ("merged", pinned, False)]:
            self.env["PR_STATE"] = state
            artifact.write_text(json.dumps({"packages": [package, {**self.package, "name": "newDependency"}]}))
            result = self.run_step("push", "Check and apply the manifest", check=False)
            self.assertEqual(result.returncode == 0, valid, result.stdout + result.stderr)

    def test_pull_request_lifecycle(self):
        script = self.root / "lifecycle.js"
        script.write_text(step("pull-request", "Synchronize the Mathlib PR")["with"]["script"])
        self.env["LIFECYCLE_SCRIPT"] = str(script)
        result = self.command("node", "--test", str(Path(__file__).with_name("mathlib_pr.test.cjs")))
        print(result.stdout)


if __name__ == "__main__":
    unittest.main()
