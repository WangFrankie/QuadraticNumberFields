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
        total_row = next(
            line for line in result.stdout.splitlines() if line.startswith("| **Total** |")
        )
        cells = [cell.strip().strip("*") for cell in total_row.strip("|").split("|")]
        code = int(cells[1])
        comment = int(cells[2])
        total = int(cells[3])
        self.assertEqual(total, code + comment)

    def test_readme_stats_preserves_following_sections(self) -> None:
        """Replacing stale statistics should preserve every following level-two section."""
        prefix = "# Fixture\n\n"
        following_sections = (
            "\n## Related Projects\n\n"
            "- [BakerHeegnerStark](https://github.com/WangFrankie/BakerHeegnerStark)\n"
            "\n## History\n\n"
            "Existing history stays unchanged.\n"
        )
        with tempfile.TemporaryDirectory() as tmpdir:
            fixture_root = Path(tmpdir)
            (fixture_root / "QNFMathlib.lean").write_text(
                "def x := 1\n-- comment\n\n", encoding="utf-8"
            )
            readme_path = fixture_root / "README.md"
            readme_path.write_text(
                prefix
                + "## Code Statistics\n\n"
                + "### Library Summary\n\n"
                + "Stale statistics to replace.\n"
                + following_sections,
                encoding="utf-8",
            )

            result = subprocess.run(
                [sys.executable, str(README_STATS_SCRIPT)],
                check=False,
                capture_output=True,
                text=True,
                cwd=fixture_root,
            )
            updated_readme = readme_path.read_text(encoding="utf-8")

        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertTrue(updated_readme.startswith(prefix + "## Code Statistics\n\n"))
        self.assertIn("| `QNFMathlib` | 1 | 1 | 2 |", updated_readme)
        self.assertNotIn("Stale statistics to replace.", updated_readme)
        self.assertTrue(updated_readme.endswith(following_sections))


if __name__ == "__main__":
    unittest.main()
