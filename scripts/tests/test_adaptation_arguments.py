"""Exercise adaptation argument parsing with local command stubs."""
import os
from pathlib import Path
import subprocess
import tempfile
import unittest

SCRIPT = Path(__file__).resolve().parents[1] / "create-adaptation-pr.sh"


class AdaptationArguments(unittest.TestCase):
    def run_script(self, arguments):
        with tempfile.TemporaryDirectory() as temporary:
            directory = Path(temporary)
            for command in ("git", "gh"):
                stub = directory / command
                stub.write_text("#!/bin/sh\nif [ \"$1\" = merge ]; then printf '%s\n' \"$*\"; exit 42; fi\nexit 0\n")
                stub.chmod(0o755)
            return subprocess.run(
                ["bash", str(SCRIPT), *arguments],
                env={**os.environ, "PATH": str(directory) + os.pathsep + os.environ["PATH"]},
                capture_output=True, text=True, check=False, timeout=5,
            )

    def test_missing_required_named_argument_reports_usage(self):
        result = self.run_script(["--bumpversion=v4.36.0", "--auto=yes"])
        self.assertNotEqual(result.returncode, 0)
        self.assertIn("Usage:", result.stdout)
        self.assertNotIn("unbound variable", result.stderr)

    def test_positional_arguments_supply_nightly_ref(self):
        result = self.run_script(["v4.36.0", "2026-10-05"])
        self.assertNotIn("unbound variable", result.stderr)
        self.assertIn("merge --no-edit origin/nightly-testing", result.stdout)
