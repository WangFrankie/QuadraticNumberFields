"""Regression tests for the Lean line counting script."""

import subprocess
import sys
import tempfile
import unittest
from pathlib import Path


REPO_ROOT = Path(__file__).resolve().parents[1]
SCRIPT = REPO_ROOT / "scripts" / "count_lean_lines.py"
README_STATS_SCRIPT = REPO_ROOT / "scripts" / "update_readme_stats.py"


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
        self.assertIn("Non-blank lines               0", result.stdout)
        self.assertIn("Blank lines                   2", result.stdout)

    def test_total_equals_code_plus_comment(self) -> None:
        """LineCount.total should exclude blank lines and equal code plus comments."""
        import importlib.util

        spec = importlib.util.spec_from_file_location("count_lean_lines", SCRIPT)
        assert spec is not None
        module = importlib.util.module_from_spec(spec)
        assert spec.loader is not None
        spec.loader.exec_module(module)

        with tempfile.TemporaryDirectory() as tmpdir:
            lean_file = Path(tmpdir) / "Mixed.lean"
            lean_file.write_text("def x := 1\n-- comment\n\n", encoding="utf-8")

            stats = module.count_lean_lines(lean_file)

        self.assertEqual(stats.code, 1)
        self.assertEqual(stats.comment, 1)
        self.assertEqual(stats.blank, 1)
        self.assertEqual(stats.total, stats.code + stats.comment)

    def test_readme_stats_total_equals_code_plus_comment(self) -> None:
        """The generated README table should keep Total Lines as code plus comments."""
        result = subprocess.run(
            [sys.executable, str(README_STATS_SCRIPT), "--dry-run"],
            check=False,
            capture_output=True,
            text=True,
            cwd=REPO_ROOT,
        )

        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertIn("| `BinaryQuadraticForms` |", result.stdout)
        self.assertIn("| `QNFMathlib` |", result.stdout)
        total_row = next(
            line for line in result.stdout.splitlines() if line.startswith("| **Total** |")
        )
        cells = [cell.strip().strip("*") for cell in total_row.strip("|").split("|")]
        code = int(cells[1])
        comment = int(cells[2])
        total = int(cells[3])
        self.assertEqual(total, code + comment)


if __name__ == "__main__":
    unittest.main()
