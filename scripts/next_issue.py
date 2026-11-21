#!/usr/bin/env python3
"""Print the number of the next free issue for an agent to take. Used by scripts/agent.sh.

    scripts/next_issue.py proof      the next proof issue, bottom-up
    scripts/next_issue.py section    the oldest free section issue
    scripts/next_issue.py proof --list [N]    show the first N choices instead (default 20)

Proof issues are handed out bottom-up: from the library file that sits lowest in the import
graph and still has a free issue, so that a section's statements are proved before work moves
to what is built on them. At most PER_FILE proofs are in flight in one file at a time, so that
agents running side by side rarely collide; when the lowest file is full the next one is used.
The limit counts this checkout's own agents (and open launcher pull requests), not issues that
outside contributors have claimed.
Issues labelled `claimed`, `blocked` or `stuck` are not free. While the file `.agent/PAUSE` exists
no issue is handed out.
"""
import collections, functools, json, pathlib, re, subprocess, sys

ROOT = pathlib.Path(__file__).resolve().parent.parent
PER_FILE = 3
WORKTREES = ROOT.parent / (ROOT.name + "-wt")     # where scripts/agent.sh puts its worktrees
MARK = re.compile(r"<!-- sorry: ([^:\s]+)::")
IMPORT = re.compile(r"^(?:public )?import (RiemannMasullo\.[A-Za-z0-9_.]+)", re.M)


def issues(label):
    # The REST listing, page by page: `gh issue list` with a label stops at 1,000 results.
    out = subprocess.run(
        ["gh", "api", "--paginate", f"repos/{{owner}}/{{repo}}/issues?state=open&labels={label}&per_page=100",
         "--jq", ".[] | select(.pull_request | not) | {number, labels: [.labels[].name], body} | tojson"],
        capture_output=True, text=True, cwd=ROOT)
    if out.returncode:
        sys.exit(out.stderr)
    return [json.loads(line) for line in out.stdout.splitlines() if line.strip()]


def in_review():
    """Issue numbers that already have an open pull request from a launcher branch. Such an
    issue can be without the `claimed` label (after a hand-in by hand, say); several agents
    sent to it at once would fight over one worktree."""
    out = subprocess.run(
        ["gh", "api", "--paginate", "repos/{owner}/{repo}/pulls?state=open&per_page=100",
         "--jq", ".[].head.ref"], capture_output=True, text=True, cwd=ROOT)
    if out.returncode:
        return set()
    found = set()
    for ref in out.stdout.split():
        m = re.fullmatch(r"(?:prover|digester)/(\d+)", ref)
        if m:
            found.add(int(m.group(1)))
    return found


def depths():
    """For each library file, the length of the longest chain of project imports below it."""
    imports = {}
    for path in (ROOT / "RiemannMasullo").rglob("*.lean"):
        rel = path.relative_to(ROOT).as_posix()
        imports[rel] = [m.replace(".", "/") + ".lean" for m in IMPORT.findall(path.read_text(errors="replace"))]

    @functools.lru_cache(maxsize=None)
    def depth(rel):
        return 1 + max((depth(d) for d in imports.get(rel, []) if d in imports), default=-1)

    sys.setrecursionlimit(10000)
    return {rel: depth(rel) for rel in imports}


def main(argv):
    # A switch for the owner of the checkout: `touch .agent/PAUSE` stops agents started with
    # `next` from taking new issues (running ones finish); `rm .agent/PAUSE` resumes.
    if (ROOT / ".agent" / "PAUSE").exists() and "--list" not in argv:
        sys.exit("paused: .agent/PAUSE exists, no new issue handed out")
    label = argv[0] if argv else "proof"
    free, busy = [], collections.Counter()
    taken_already = in_review()
    for issue in issues(label):
        m = MARK.search(issue["body"] or "")
        file = m.group(1) if m else "-"
        if "claimed" in issue["labels"] or issue["number"] in taken_already:
            # Taken, so not free. Only this checkout's own agents count toward the limit per
            # file: a file whose issues are claimed by outside contributors is not full for us,
            # or the lowest files would wait on whoever claimed three issues there.
            if issue["number"] in taken_already or any(
                    (WORKTREES / f"{role}-{issue['number']}").exists() for role in ("prover", "digester")):
                busy[file] += 1
        elif not {"blocked", "stuck"} & set(issue["labels"]):
            free.append((file, issue["number"]))
    if label != "proof":
        order = sorted(free, key=lambda fn: fn[1])
    else:
        depth = depths()
        ranked = sorted(free, key=lambda fn: (depth.get(fn[0], 10**6), fn[0], fn[1]))
        # Within the bottom-up order, skip files that already have enough proofs in flight.
        taken, order, rest = collections.Counter(busy), [], []
        for file, number in ranked:
            if taken[file] < PER_FILE:
                taken[file] += 1
                order.append((file, number))
            else:
                rest.append((file, number))
        order += rest
    if "--list" in argv:
        i = argv.index("--list")
        count = int(argv[i + 1]) if len(argv) > i + 1 else 20
        for file, number in order[:count]:
            print(f"#{number}\t{file}\t(in flight there: {busy[file]})")
        return 0
    if not order:
        return 1
    print(order[0][1])
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
