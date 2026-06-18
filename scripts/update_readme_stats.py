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
]


class LineCount(NamedTuple):
    total: int
    code: int
    comment: int
    blank: int


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


def get_module_stats(files: list[Path]) -> dict[str, LineCount]:
    """Group files by module and compute stats"""
    modules: dict[str, LineCount] = {}
    
    for f in files:
        stats = count_lean_lines(f)
        
        # Get relative path from repository root
        rel_path = f.relative_to(Path('.'))
        parts = rel_path.parts
        
        if len(parts) == 1 and rel_path.suffix == ".lean":
            module = rel_path.stem
        elif parts[0] in {"QNFMathlib", "BinaryQuadraticForms"}:
            module = parts[0]
        elif len(parts) >= 3 and parts[0] == 'QuadraticNumberFields':
            # File in a top-level subpackage: one row per subpackage.
            module = f"QuadraticNumberFields/{parts[1]}"
        elif len(parts) == 2 and parts[0] == 'QuadraticNumberFields':
            # File directly under QuadraticNumberFields/.
            module = "QuadraticNumberFields"
        else:
            module = "Root"
        
        if module not in modules:
            modules[module] = LineCount(0, 0, 0, 0)
        
        modules[module] = LineCount(
            modules[module].total + stats.total,
            modules[module].code + stats.code,
            modules[module].comment + stats.comment,
            modules[module].blank + stats.blank,
        )
    
    return modules


def generate_code_stats_markdown(files: list[Path]) -> str:
    """Generate markdown for code statistics"""
    modules = get_module_stats(files)
    
    # Calculate totals (column sums, so the Total row matches the table)
    total_code = sum(m.code for m in modules.values())
    total_comment = sum(m.comment for m in modules.values())
    total_lines = sum(m.total for m in modules.values())
    
    # Sort modules by code lines (descending)
    sorted_modules = sorted(modules.items(), key=lambda x: x[1].code, reverse=True)
    
    md = "## Code Statistics\n\n"
    md += "| Module | Code Lines | Comment Lines | Total Lines |\n"
    md += "|--------|------------|---------------|-------------|\n"
    
    for module, stats in sorted_modules:
        md += f"| `{module}` | {stats.code} | {stats.comment} | {stats.total} |\n"
    
    md += f"| **Total** | **{total_code}** | **{total_comment}** | **{total_lines}** |\n"
    
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
    
    # Pattern to find the code statistics section
    pattern = r'(## Code Statistics\n\n\| Module.*?\*\*Total\*\* \|.*?\n)'
    
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
