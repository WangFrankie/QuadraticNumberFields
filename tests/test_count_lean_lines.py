"""Regression tests for the Lean line counting script."""

import subprocess
import sys
import tempfile
import unittest
from pathlib import Path


REPO_ROOT = Path(__file__).resolve().parents[1]
SCRIPT = REPO_ROOT / "scripts" / "count_lean_lines.py"


class CountLeanLinesCliTest(unittest.TestCase):
    """CLI behavior for edge-case Lean inputs."""

    def test_blank_only_file_does_not_crash(self) -> None:
        """A directory containing only blank Lean lines should still report stats."""
        with tempfile.TemporaryDirectory() as tmpdir:
            lean_file = Path(tmpdir) / "Blank.lean"
            lean_file.write_text("\n\n", encoding="utf-8")

            result = subprocess.run(
                [sys.executable, str(SCRIPT), tmpdir],
                check=False,
                capture_output=True,
                text=True,
            )

        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertIn("Total lines                   0", result.stdout)
        self.assertIn("Blank lines                   2", result.stdout)


if __name__ == "__main__":
    unittest.main()
