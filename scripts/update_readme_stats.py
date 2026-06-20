#!/usr/bin/env python3
"""
Generate code statistics and update README.md with the stats.
This script is run by the pre-commit hook in .githooks/ to keep the
README up-to-date.
"""

import os
import re
from pathlib import Path
from typing import NamedTuple
import sys


README_LEAN_ROOTS = [
    "QNFMathlib.lean",
    "QNFMathlib",
    "BinaryQuadraticForms.lean",
    "BinaryQuadraticForms",
    "QuadraticNumberFields.lean",
    "QuadraticNumberFields",
    "FormClassGroup.lean",
    "FormClassGroup",
    "ImaginaryClassNumberOne.lean",
    "ImaginaryClassNumberOne",
    "Examples.lean",
    "Examples",
]


class LineCount(NamedTuple):
    total: int
    code: int
    comment: int
    blank: int


class ModuleKey(NamedTuple):
    library: str
    subtree: str


def add_counts(left: LineCount, right: LineCount) -> LineCount:
    """Add two line-count records."""
    return LineCount(
        left.total + right.total,
        left.code + right.code,
        left.comment + right.comment,
        left.blank + right.blank,
    )


def count_lean_lines(file_path: Path) -> LineCount:
    """Count lines in a single Lean file"""
    with open(file_path, 'r', encoding='utf-8') as f:
        lines = f.readlines()
    
    blank = 0
    comment = 0
    code = 0
    
    in_block_comment = False
    
    for line in lines:
        stripped = line.strip()
        
        if not stripped:
            blank += 1
            continue
        
        if in_block_comment:
            comment += 1
            if '-/' in stripped:
                in_block_comment = False
            continue
        
        if '/-' in stripped:
            comment += 1
            if '-/' in stripped and stripped.index('-/') > stripped.index('/-'):
                continue
            in_block_comment = True
            continue
        
        if stripped.startswith('--'):
            comment += 1
            continue
        
        code += 1
    
    return LineCount(total=code + comment, code=code, comment=comment, blank=blank)


def walk_lean_files(root_dirs: str | list[str], exclude_dirs: list[str] | None = None) -> list[Path]:
    """Walk through all Lean files"""
    if exclude_dirs is None:
        exclude_dirs = ['.lake', 'node_modules', '.git']
    
    lean_files: list[Path] = []
    roots = [root_dirs] if isinstance(root_dirs, str) else root_dirs

    for root_dir in roots:
        root = Path(root_dir)
        if not root.exists():
            continue
        if root.is_file():
            if root.suffix == ".lean":
                lean_files.append(root)
            continue
        for dirpath, dirnames, filenames in os.walk(root):
            dirnames[:] = [d for d in dirnames if d not in exclude_dirs]
            for filename in filenames:
                if filename.endswith('.lean'):
                    lean_files.append(Path(dirpath) / filename)

    return lean_files


def module_key(file_path: Path) -> ModuleKey:
    """Classify a Lean file by Lake library root and immediate subtree."""
    rel_path = file_path.relative_to(Path('.'))
    parts = rel_path.parts

    if len(parts) == 1 and rel_path.suffix == ".lean":
        return ModuleKey(rel_path.stem, rel_path.name)

    if parts[0] in {
            "QNFMathlib",
            "BinaryQuadraticForms",
            "FormClassGroup",
            "ImaginaryClassNumberOne",
            "Examples",
    }:
        subtree = f"{parts[1]}/" if len(parts) >= 3 else parts[1]
        return ModuleKey(parts[0], subtree)

    if parts[0] == "QuadraticNumberFields":
        subtree = f"{parts[1]}/" if len(parts) >= 3 else parts[1]
        return ModuleKey("QuadraticNumberFields", subtree)

    return ModuleKey("Root", str(rel_path))


def get_library_tree_stats(files: list[Path]) -> dict[str, dict[str, LineCount]]:
    """Group files by library and immediate subtree."""
    libraries: dict[str, dict[str, LineCount]] = {}

    for file_path in files:
        key = module_key(file_path)
        stats = count_lean_lines(file_path)
        libraries.setdefault(key.library, {})
        libraries[key.library].setdefault(key.subtree, LineCount(0, 0, 0, 0))
        libraries[key.library][key.subtree] = add_counts(
            libraries[key.library][key.subtree],
            stats,
        )

    return libraries


def library_totals(libraries: dict[str, dict[str, LineCount]]) -> dict[str, LineCount]:
    """Compute one aggregate row for each library."""
    totals: dict[str, LineCount] = {}
    for library, subtrees in libraries.items():
        total = LineCount(0, 0, 0, 0)
        for stats in subtrees.values():
            total = add_counts(total, stats)
        totals[library] = total
    return totals


def generate_code_stats_markdown(files: list[Path]) -> str:
    """Generate markdown for code statistics"""
    libraries = get_library_tree_stats(files)
    summaries = library_totals(libraries)
    
    # Calculate totals (column sums, so the Total row matches the table)
    total_code = sum(m.code for m in summaries.values())
    total_comment = sum(m.comment for m in summaries.values())
    total_lines = sum(m.total for m in summaries.values())
    
    # Sort modules by code lines (descending)
    sorted_libraries = sorted(summaries.items(), key=lambda x: x[1].code, reverse=True)
    
    md = "## Code Statistics\n\n"
    md += "Counts exclude blank lines.\n\n"
    md += "### Library Summary\n\n"
    md += "| Library | Code Lines | Comment Lines | Total Lines |\n"
    md += "|--------|------------|---------------|-------------|\n"
    
    for library, stats in sorted_libraries:
        md += f"| `{library}` | {stats.code} | {stats.comment} | {stats.total} |\n"
    
    md += f"| **Total** | **{total_code}** | **{total_comment}** | **{total_lines}** |\n"
    md += "\n### Library Tree\n"

    for library, library_stats in sorted_libraries:
        md += f"\n#### `{library}`\n\n"
        md += "| Subtree | Code Lines | Comment Lines | Total Lines |\n"
        md += "|--------|------------|---------------|-------------|\n"
        sorted_subtrees = sorted(
            libraries[library].items(),
            key=lambda x: (x[0] != f"{library}.lean", x[0]),
        )
        for index, (subtree, stats) in enumerate(sorted_subtrees):
            connector = "└──" if index == len(sorted_subtrees) - 1 else "├──"
            md += f"| `{connector} {subtree}` | {stats.code} | {stats.comment} | {stats.total} |\n"
        md += (
            f"| **{library} total** | **{library_stats.code}** | "
            f"**{library_stats.comment}** | **{library_stats.total}** |\n"
        )
    
    return md


def update_readme(readme_path: str = "README.md") -> None:
    """Update README.md with current code statistics"""
    exclude_dirs = ['.git', 'node_modules', '.lake']
    
    files = walk_lean_files(README_LEAN_ROOTS, exclude_dirs)
    
    if not files:
        print("No .lean files found")
        sys.exit(1)
    
    stats_markdown = generate_code_stats_markdown(files)
    
    with open(readme_path, 'r', encoding='utf-8') as f:
        readme_content = f.read()
    
    # Pattern to find the code statistics section.
    pattern = r'## Code Statistics\n\n.*?(?=\n## History)'
    
    match = re.search(pattern, readme_content, re.DOTALL)
    
    if match:
        # Replace existing section
        new_readme = readme_content[:match.start()] + stats_markdown + readme_content[match.end():]
    else:
        # Insert before the History section, or append at the end
        history_match = re.search(r'^## History$', readme_content, re.MULTILINE)
        if history_match:
            insert_pos = history_match.start()
            new_readme = (readme_content[:insert_pos] + stats_markdown + "\n"
                          + readme_content[insert_pos:])
        else:
            new_readme = readme_content.rstrip('\n') + "\n\n" + stats_markdown
    
    with open(readme_path, 'w', encoding='utf-8') as f:
        f.write(new_readme)
    
    print(f"Updated README.md with code statistics")


def main():
    import argparse
    
    parser = argparse.ArgumentParser(description='Generate code statistics for README')
    parser.add_argument('--readme', default='README.md', help='Path to README file')
    parser.add_argument('--dry-run', action='store_true', help='Print stats without updating README')
    
    args = parser.parse_args()
    
    exclude_dirs = ['.git', 'node_modules', '.lake']
    files = walk_lean_files(README_LEAN_ROOTS, exclude_dirs)
    
    if not files:
        print("No .lean files found")
        sys.exit(1)
    
    stats_markdown = generate_code_stats_markdown(files)
    
    if args.dry_run:
        print(stats_markdown)
    else:
        update_readme(args.readme)


if __name__ == '__main__':
    main()
