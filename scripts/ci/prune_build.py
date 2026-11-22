#!/usr/bin/env python3
"""Delete build outputs of library modules whose source file no longer exists.

    scripts/ci/prune_build.py [--root DIR] [--dry-run]

An incremental build keeps whatever the previous build left. When a module is deleted or renamed,
its `.olean` and the rest would stay in `.lake/build`, where `lake env lean` and the comparator
could still import it, and the saved archive would only grow. This removes every file under
`.lake/build/lib/lean/RiemannMasullo/` and `.lake/build/ir/RiemannMasullo/` whose module has no
`RiemannMasullo/….lean`, and directories left empty. Used by the Main state workflow.
"""
import sys
from pathlib import Path

LIB = "RiemannMasullo"


def orphans(root):
    """Build outputs under `root`/.lake/build that belong to no source file."""
    found = []
    for sub in ("lib/lean", "ir"):
        top = root / ".lake" / "build" / sub / LIB
        if not top.is_dir():
            continue
        for path in sorted(top.rglob("*")):
            if path.is_file():
                rel = path.relative_to(top)
                module = rel.parent / rel.name.split(".", 1)[0]      # Sec2b.olean.private.hash -> Sec2b
                if not (root / LIB / module).with_suffix(".lean").is_file():
                    found.append(path)
    return found


def prune(root, dry=False):
    found = orphans(root)
    for path in found:
        print(("would delete " if dry else "deleted ") + str(path.relative_to(root)))
        if not dry:
            path.unlink()
    if not dry:
        for sub in ("lib/lean", "ir"):
            top = root / ".lake" / "build" / sub / LIB
            if top.is_dir():
                for path in sorted((p for p in top.rglob("*") if p.is_dir()), reverse=True):
                    if not any(path.iterdir()):
                        path.rmdir()
    return len(found)


if __name__ == "__main__":
    args = sys.argv[1:]
    root = Path(args[args.index("--root") + 1]) if "--root" in args else Path.cwd()
    count = prune(root, dry="--dry-run" in args)
    print(f"{count} orphaned build file(s)")
