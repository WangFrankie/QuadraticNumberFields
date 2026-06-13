#!/usr/bin/env python3
"""
Count lines in Lean code files (with and without comments)
"""

import os
from pathlib import Path
from typing import NamedTuple


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
        
        # Empty line
        if not stripped:
            blank += 1
            continue
        
        # Block comment /- ... -/
        if in_block_comment:
            comment += 1
            if '-/' in stripped:
                in_block_comment = False
            continue
        
        # Block comment start
        if '/-' in stripped:
            comment += 1
            if '-/' in stripped and stripped.index('-/') > stripped.index('/-'):
                # Single-line block comment /- ... -/
                continue
            in_block_comment = True
            continue
        
        # Line comment -- ...
        if stripped.startswith('--'):
            comment += 1
            continue
        
        # Code line
        code += 1
    
    return LineCount(total=code + comment, code=code, comment=comment, blank=blank)


def walk_lean_files(root_dir: str, exclude_dirs: list[str] = None) -> list[Path]:
    """Walk through all Lean files"""
    if exclude_dirs is None:
        exclude_dirs = ['.lake', 'node_modules', '.git']
    
    lean_files = []
    root = Path(root_dir)
    
    for dirpath, dirnames, filenames in os.walk(root):
        # Exclude specified directories
        dirnames[:] = [d for d in dirnames if d not in exclude_dirs]
        
        for filename in filenames:
            if filename.endswith('.lean'):
                lean_files.append(Path(dirpath) / filename)
    
    return lean_files


def print_file_stats(files: list[Path], verbose: bool = False):
    """Print per-file statistics"""
    all_stats = []
    
    for f in sorted(files):
        stats = count_lean_lines(f)
        all_stats.append((f, stats))
        
        if verbose:
            try:
                rel_path = f.relative_to(Path.cwd())
            except ValueError:
                rel_path = f
            print(
                f"{rel_path}: {stats.total:4d} non-blank, {stats.code:4d} code, "
                f"{stats.comment:4d} comment, {stats.blank:4d} blank"
            )
    
    return all_stats


def percentage(part: int, whole: int) -> float:
    """Return ``part`` as a percentage of ``whole``, treating empty inputs as 0%."""
    if whole == 0:
        return 0.0
    return part / whole * 100


def main():
    import argparse
    
    parser = argparse.ArgumentParser(description='Count lines in Lean code files')
    parser.add_argument(
        'path',
        nargs='?',
        default='QuadraticNumberFields',
        help='Directory to analyze (default: QuadraticNumberFields)',
    )
    parser.add_argument(
        '-v',
        '--verbose',
        action='store_true',
        help='Show detailed stats for each file',
    )
    parser.add_argument(
        '-e',
        '--exclude',
        nargs='*',
        default=[],
        help='Additional directories to exclude',
    )
    parser.add_argument(
        '--no-exclude-lake',
        action='store_true',
        help='Do not exclude .lake directory',
    )
    
    args = parser.parse_args()
    
    exclude_dirs = ['.git', 'node_modules'] + args.exclude
    if not args.no_exclude_lake:
        exclude_dirs.append('.lake')
    
    files = walk_lean_files(args.path, exclude_dirs)
    
    if not files:
        print(f"No .lean files found in {args.path}")
        return
    
    print(f"Directory: {args.path}")
    print(f"Excluded: {exclude_dirs}")
    print(f"Files found: {len(files)}\n")
    
    if args.verbose:
        print_file_stats(files, verbose=True)
        print()
    
    # Aggregate stats
    total_lines = 0
    total_code = 0
    total_comment = 0
    total_blank = 0
    
    for f, stats in print_file_stats(files, verbose=False):
        total_lines += stats.total
        total_code += stats.code
        total_comment += stats.comment
        total_blank += stats.blank
    
    print("=" * 60)
    print(f"{'Category':<20} {'Lines':>10} {'Percent':>10}")
    print("-" * 60)
    physical_lines = total_lines + total_blank
    print(f"{'Non-blank lines':<20} {total_lines:>10}")
    print(f"{'Code lines':<20} {total_code:>10} {percentage(total_code, physical_lines):>9.1f}%")
    print(
        f"{'Comment lines':<20} {total_comment:>10} "
        f"{percentage(total_comment, physical_lines):>9.1f}%"
    )
    print(f"{'Blank lines':<20} {total_blank:>10} {percentage(total_blank, physical_lines):>9.1f}%")
    print("=" * 60)
    print(f"\nCode lines (excluding comments): {total_code}")
    print(f"Non-blank lines (code + comments): {total_lines}")


if __name__ == '__main__':
    main()
