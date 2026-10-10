import subprocess
import tempfile
import unittest
from pathlib import Path

SCRIPT = Path(__file__).resolve().parents[1] / "lintWhitespace.sh"


class WhitespaceLintTests(unittest.TestCase):
    def test_files(self):
        for content, expected in ((b"", 0), (b"def x := 1\n", 0),
                                  (b"def x := 1", 1), (b"def x := 1 \n", 1),
                                  (b"def x := 1\t\n", 1)):
            with self.subTest(content=content), tempfile.TemporaryDirectory() as tmp:
                root = Path(tmp)
                (root / "Batteries").mkdir()
                (root / "Batteries" / "name with\nnewline.lean").write_bytes(content)
                result = subprocess.run(["bash", str(SCRIPT)], cwd=root, capture_output=True)
                self.assertEqual(result.returncode, expected, result.stdout + result.stderr)

    def test_wrong_directory_fails(self):
        with tempfile.TemporaryDirectory() as tmp:
            result = subprocess.run(["bash", str(SCRIPT)], cwd=tmp, capture_output=True)
            self.assertNotEqual(result.returncode, 0)
