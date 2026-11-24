"""Check that command arguments are not interpreted as shell programs."""
import json
import os
from pathlib import Path
import subprocess
import tempfile
import unittest

SCRIPT = Path(__file__).resolve().parents[1] / "create-adaptation-pr.sh"


class AdaptationLiteralCommands(unittest.TestCase):
    def test_title_and_message_preserve_literal_shell_text(self):
        with tempfile.TemporaryDirectory() as temporary:
            directory = Path(temporary)
            git = directory / "git"
            git.write_text("#!/bin/sh\nif [ \"$1\" = diff ] && [ \"$3\" != --diff-filter=U ]; then echo changed; fi\nexit 0\n")
            git.chmod(0o755)
            for command in ("gh", "zulip-send"):
                stub = directory / command
                stub.write_text("#!/usr/bin/env python3\nimport json,os,sys\nwith open(os.environ['ADAPTATION_TEST_ARGS'], 'a') as stream: stream.write(json.dumps(sys.argv[1:]) + '\\n')\nprint('https://github.com/leanprover-community/batteries/pull/123')\n")
                stub.chmod(0o755)
            log = directory / "arguments"
            date = "2026-10-05$(>unexpected)"
            result = subprocess.run(
                ["bash", str(SCRIPT), "--bumpversion=v4.36.0",
                 "--nightlydate=" + date, "--nightlysha=deadbeef", "--auto=yes"],
                cwd=directory,
                env={**os.environ, "PATH": str(directory) + os.pathsep + os.environ["PATH"],
                     "ADAPTATION_TEST_ARGS": str(log)},
                capture_output=True, text=True, check=False, timeout=5,
            )
            self.assertEqual(result.returncode, 0, result.stderr)
            self.assertFalse((directory / "unexpected").exists())
            commands = [json.loads(line) for line in log.read_text().splitlines()]
            self.assertIn("chore: adaptations for nightly-" + date, commands[0])
            self.assertIn("batteries#123 adaptations for nightly-" + date, commands[1])
