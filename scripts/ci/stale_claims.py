#!/usr/bin/env python3
"""Release claims on proof issues that have gone quiet (issues labelled `proof` and `claimed`).

    scripts/ci/stale_claims.py            list what would be released
    scripts/ci/stale_claims.py --apply    release them

A claim is released when its `Claiming` comment is older than HOURS and no open pull request
refers to the issue (a closing keyword with the issue number, or a branch `prover/<n>`). The
issue loses the `claimed` label and its assignees and gets a comment; anyone, including the
previous holder, can claim it again. Run hourly by the `Claims` workflow.
"""
import datetime, json, re, subprocess, sys

HOURS = 8
CLAIM = re.compile(r"\s*claim(ing|ed)?([^a-z]|$)", re.I)
CLOSES = re.compile(r"\b(?:close[sd]?|fix(?:e[sd])?|resolve[sd]?)\s*:?\s+#(\d+)", re.I)
BRANCH = re.compile(r"(?:prover|digester)/(\d+)")


def referenced(pulls):
    """Issue numbers that an open pull request says it closes or is named after."""
    found = set()
    for pull in pulls:
        found.update(int(n) for n in CLOSES.findall((pull.get("title") or "") + "\n" + (pull.get("body") or "")))
        m = BRANCH.fullmatch(pull.get("ref") or "")
        if m:
            found.add(int(m.group(1)))
    return found


def last_claim(comments):
    """Time of the newest comment whose first line claims the issue, or None."""
    times = [c["created_at"] for c in comments if CLAIM.match((c.get("body") or "").split("\n", 1)[0])]
    return max(times) if times else None


def is_stale(claimed_at, now, hours=HOURS):
    then = datetime.datetime.fromisoformat(claimed_at.replace("Z", "+00:00"))
    return (now - then).total_seconds() > hours * 3600


def api(*args):
    out = subprocess.run(["gh", "api", "--paginate", *args], capture_output=True, text=True)
    if out.returncode:
        sys.exit(out.stderr)
    return [json.loads(line) for line in out.stdout.splitlines() if line.strip()]


def main(argv):
    apply = "--apply" in argv
    now = datetime.datetime.now(datetime.timezone.utc)
    pulls = api("repos/{owner}/{repo}/pulls?state=open&per_page=100",
                "--jq", ".[] | {title, body, ref: .head.ref} | tojson")
    live = referenced(pulls)
    issues = api("repos/{owner}/{repo}/issues?state=open&labels=proof,claimed&per_page=100",
                 "--jq", ".[] | select(.pull_request | not) | {number, assignees: [.assignees[].login]} | tojson")
    released = 0
    for issue in issues:
        n = issue["number"]
        if n in live:
            continue
        comments = api(f"repos/{{owner}}/{{repo}}/issues/{n}/comments?per_page=100",
                       "--jq", ".[] | {body, created_at} | tojson")
        claimed_at = last_claim(comments)
        if claimed_at is None or not is_stale(claimed_at, now):
            continue
        released += 1
        print(f"#{n}: claimed {claimed_at}, by {', '.join(issue['assignees']) or 'a project agent'}")
        if apply:
            subprocess.run(["gh", "issue", "comment", str(n), "--body",
                            f"This claim has been released automatically: it is more than {HOURS} hours old and "
                            "no open pull request refers to this issue. If you are still working on it, "
                            "comment `Claiming` again; you are welcome to, and nothing is lost."],
                           capture_output=True)
            cmd = ["gh", "issue", "edit", str(n), "--remove-label", "claimed"]
            if issue["assignees"]:
                cmd += ["--remove-assignee", ",".join(issue["assignees"])]
            subprocess.run(cmd, capture_output=True)
    print(f"{released} stale claim(s) of {len(issues)} claimed issues" + ("" if apply else "; dry run"))


if __name__ == "__main__":
    main(sys.argv[1:])
