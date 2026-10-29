"""Ensure non-conflict merge errors stop the adaptation workflow."""
import os
from pathlib import Path
import subprocess
import tempfile
import unittest

SCRIPT = Path(__file__).resolve().parents[1] / "create-adaptation-pr.sh"


class AdaptationMergeErrors(unittest.TestCase):
    def test_merge_error_stops_before_any_push(self):
        with tempfile.TemporaryDirectory() as temporary:
            directory = Path(temporary)
            log = directory / "commands"
            git = directory / "git"
            git.write_text("#!/bin/sh\nprintf '%s\n' \"$*\" >> \"$ADAPTATION_TEST_LOG\"\n[ \"$1\" != merge ] || exit 2\nexit 0\n")
            git.chmod(0o755)
            gh = directory / "gh"
            gh.write_text("#!/bin/sh\nexit 0\n")
            gh.chmod(0o755)
            result = subprocess.run(
                ["bash", str(SCRIPT), "--bumpversion=v4.36.0",
                 "--nightlydate=2026-10-05", "--nightlysha=deadbeef", "--auto=yes"],
                env={**os.environ, "PATH": str(directory) + os.pathsep + os.environ["PATH"],
                     "ADAPTATION_TEST_LOG": str(log)},
                capture_output=True, text=True, check=False, timeout=5,
            )
            self.assertNotEqual(result.returncode, 0)
            self.assertNotIn("push", log.read_text())
