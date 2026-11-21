"""Check a local triage report against a PR head and the current main commit."""

import os
import re
import subprocess
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent / "ci"))
from auto_merge import Merger


def changed_paths(before, after):
    data = subprocess.check_output(
        ["git", "diff", "--name-only", "--no-renames", "-z", before, after, "--"]
    )
    return [os.fsdecode(name) for name in data.split(b"\0") if name]


def stale_reason(report, head, tip):
    with report.open("rb") as source:
        header = source.readline(160).rstrip(b"\n")
    match = re.fullmatch(rb"checking ([0-9a-f]{40}) against ([0-9a-f]{40})", header)
    if not match or match[1].decode() != head:
        return "report does not identify the reviewed head and base"
    base = match[2].decode()
    if base == tip:
        return None
    if subprocess.run(["git", "merge-base", "--is-ancestor", base, tip]).returncode:
        return "the checked base is no longer an ancestor of main"

    # Compare the PR to its fork point and main to the exact snapshot that was built.
    fork = subprocess.check_output(["git", "merge-base", base, head], text=True).strip()
    paths = set(changed_paths(fork, head))
    # Local reports also depend on the wrapper that ran the build.
    paths.add("scripts/check_pr.sh")
    count = int(subprocess.check_output(["git", "rev-list", "--count", f"{base}..{tip}"]))
    updates = changed_paths(base, tip)
    return Merger.moved(
        {"status": "ahead", "ahead_by": count, "files": [{"filename": f} for f in updates]},
        paths,
    )


if __name__ == "__main__":
    try:
        reason = stale_reason(Path(sys.argv[1]), sys.argv[2], sys.argv[3])
    except (OSError, subprocess.CalledProcessError) as error:
        sys.exit(f"could not verify the report: {error}")
    if reason:
        print(reason)
        sys.exit(1)
