#!/usr/bin/env python3
"""Keep `proof` issues in step with the `sorry`s in RiemannMasullo/.

    scripts/issues.py            show what would change
    scripts/issues.py --apply    open an issue per new sorry, close issues whose sorry is gone,
                                 and unblock section issues whose prerequisites are closed

Run from an up-to-date `main`. Lean itself reports the sorries (`lake build` warnings), so this
never misreads the source. An issue is tied to its declaration by a hidden marker in the body.
A section issue lists the issues it waits for in a marker `<!-- needs: 12 15 -->`; when all of
them are closed, its `blocked` label is removed.
"""
import json, pathlib, re, subprocess, sys, time

ROOT = pathlib.Path(__file__).resolve().parent.parent
WARN = re.compile(r"warning: (RiemannMasullo/\S+?\.lean):(\d+):(\d+): declaration uses `sorry`")
MARK = re.compile(r"<!-- sorry: (\S+) -->")
DECL = re.compile(r"\s*(@\[[^\]]*\]\s*)*((private|protected|noncomputable|nonrec|unsafe|partial|public|meta)\s+)*"
                  r"(theorem|lemma|def|instance|abbrev|example|structure|class|inductive|opaque)\b")


def run(cmd, **kw):
    return subprocess.run(cmd, cwd=ROOT, capture_output=True, text=True, **kw)


def list_issues(state, label):
    """All issues with a label, through the REST listing. `gh issue list` with a label goes
    through GitHub's search, which stops at 1,000 results, and a truncated list of open proof
    issues makes this script open duplicates."""
    out = run(["gh", "api", "--paginate",
               f"repos/{{owner}}/{{repo}}/issues?state={state}&labels={label}&per_page=100",
               "--jq", ".[] | select(.pull_request | not) | {number, state, title, body} | tojson"])
    if out.returncode:
        sys.exit(out.stderr)
    return [json.loads(line) for line in out.stdout.splitlines() if line.strip()]


def sorries():
    out = run(["lake", "build", "RiemannMasullo"])
    if out.returncode:
        sys.exit("lake build failed; fix the build first\n" + (out.stdout + out.stderr)[-3000:])
    found = {}
    for path, line, col in WARN.findall(out.stdout + out.stderr):
        lines = (ROOT / path).read_text().splitlines()
        i = int(line) - 1
        # The warning points into the file as Lean compiled it. If the file on disk is another
        # version (the checkout moved during the build), the position lands on arbitrary text
        # and everything below would be read off the wrong lines. Stop instead.
        if i >= len(lines) or not DECL.match(lines[i]):
            sys.exit(f"{path}:{line}: the build reports a `sorry` here, but this line of the file is "
                     "not a declaration. The checkout does not match the build (did it change "
                     "during the run?). Nothing was changed; update, rebuild and run again.")
        name = re.match(r"[^\s:({\[]+", lines[i][int(col):])
        name = name.group(0) if name else f"line{line}"
        top = i
        while top > 0 and lines[top - 1].lstrip().startswith("@["):
            top -= 1
        if top > 0 and lines[top - 1].rstrip().endswith("-/"):
            top -= 1
            while top > 0 and "/--" not in lines[top]:
                top -= 1
        end = i
        while end < len(lines) - 1 and "sorry" not in lines[end] and end - i < 80:
            end += 1
        block = "\n".join(lines[top:end + 1])
        paper = re.search(r"Paper:\s*(.*?\bpp?\.\s*\d+(?:[-–]\d+)?)", block)
        found[f"{path}::{name}"] = dict(path=path, line=int(line), name=name, block=block,
                                        paper=paper.group(1) if paper else "")
    return found


def chapter_label(path):
    m = re.match(r"RiemannMasullo/(Ch\d+|App[A-E])", path)
    return m.group(1)[0].lower() + m.group(1)[1:] if m else None


def at_main():
    """Whether this checkout is at the tip of origin/main. Applying from an older commit would
    close the issues of every `sorry` added since, and reopen those proved since."""
    run(["git", "fetch", "-q", "origin", "main"])
    head = run(["git", "rev-parse", "HEAD"]).stdout.strip()
    tip = run(["git", "rev-parse", "origin/main"]).stdout.strip()
    return head == tip, head[:7], tip[:7]


def main():
    apply = "--apply" in sys.argv
    if apply:
        # The integrator and the merger may both run this, from different checkouts. One at a
        # time, so that neither opens an issue the other has just opened.
        import fcntl
        common = run(["git", "rev-parse", "--path-format=absolute", "--git-common-dir"]).stdout.strip()
        lockdir = pathlib.Path(common).parent / ".agent"
        lockdir.mkdir(exist_ok=True)
        global _lock
        _lock = open(lockdir / "issues.lock", "w")
        fcntl.flock(_lock, fcntl.LOCK_EX)
        # A checkout a few merges behind is handled below. One far behind is refused.
        run(["git", "fetch", "-q", "origin", "main"])
        behind = int(run(["git", "rev-list", "--count", "HEAD..origin/main"]).stdout.strip() or 0)
        if behind > 40:
            sys.exit(f"this checkout is {behind} commits behind origin/main: update it, then rerun")
    branch = run(["git", "rev-parse", "--abbrev-ref", "HEAD"]).stdout.strip()
    if branch != "main":
        print(f"note: on branch {branch}, not main", file=sys.stderr)
    sha = run(["git", "rev-parse", "--short", "HEAD"]).stdout.strip()
    full_sha = run(["git", "rev-parse", "HEAD"]).stdout.strip()
    url = run(["gh", "repo", "view", "--json", "url", "--jq", ".url"]).stdout.strip()
    state = lambda: (run(["git", "rev-parse", "HEAD"]).stdout.strip(),
                     run(["git", "status", "--porcelain", "--untracked-files=no", "--", "RiemannMasullo"]).stdout)
    before = state()
    current = sorries()
    if state() != before:
        sys.exit("the checkout changed while this ran (another commit was checked out, or files "
                 "were edited). Nothing was changed; run again from a checkout nobody else is using.")
    open_issues = {}
    for issue in sorted(list_issues("open", "proof"), key=lambda i: -i["number"]):
        m = MARK.search(issue["body"] or "")
        if m:
            open_issues[m.group(1)] = issue["number"]      # the oldest issue wins

    new = [k for k in current if k not in open_issues]
    stale = [k for k in open_issues if k not in current]
    # `main` moves while this runs, and the checkout may be a few merges behind. What this
    # checkout cannot know about is left alone: a `sorry` whose issue was closed after this
    # commit was made (it has just been proved), and an issue opened after it (its `sorry` is
    # newer than this checkout). The next run, from a later commit, settles both.
    head_time = run(["git", "show", "-s", "--format=%cI", "HEAD"]).stdout.strip()
    since = run(["date", "-u", "-d", f"{head_time} - 2 minutes", "+%Y-%m-%dT%H:%M:%SZ"]).stdout.strip()
    recent = run(["gh", "api", "--paginate",
                  f"repos/{{owner}}/{{repo}}/issues?state=all&labels=proof&since={since}&per_page=100",
                  "--jq", ".[] | select(.pull_request | not) | {number, state, body, created_at} | tojson"])
    if recent.returncode:
        sys.exit(recent.stderr)
    recent = [json.loads(line) for line in recent.stdout.splitlines() if line.strip()]
    just_closed = {m.group(1) for i in recent if i["state"] == "closed"
                   for m in [MARK.search(i["body"] or "")] if m}
    just_opened = {i["number"] for i in recent if i["created_at"] >= since}
    skipped = [k for k in new if k in just_closed] + [k for k in stale if open_issues[k] in just_opened]
    new = [k for k in new if k not in just_closed]
    stale = [k for k in stale if open_issues[k] not in just_opened]
    if skipped:
        print(f"note: {len(skipped)} left for the next run (changed on main after {sha})")
    print(f"{len(current)} sorries at {sha}; {len(open_issues)} open proof issues; "
          f"{len(new)} to open, {len(stale)} to close")
    if apply and len(new) > 20 and len(stale) > 20 and "--force" not in sys.argv:
        sys.exit(f"this would open {len(new)} issues and close {len(stale)} at once. That is what a "
                 "mismatch between the build and the files looks like (2026-11-21: 110 issues with "
                 "garbled names opened, 150 good ones closed). Look at the dry run; if it is right, "
                 "pass --force.")
    for key in new:
        s = current[key]
        title = f"Prove `{s['name']}`" + (f" ({s['paper']})" if s["paper"] else "")
        body = (f"[`{s['path']}`, line {s['line']}]({url}/blob/{full_sha}/{s['path']}#L{s['line']})\n\n"
                f"```lean\n{s['block']}\n```\n\n"
                "Replace the `sorry` with a proof, or split it into smaller lemmas, without changing "
                "the statement. If the statement looks wrong, say so here instead.\n\n"
                "**To take this issue**, comment `Claiming`, then follow "
                f"[CONTRIBUTING.md]({url}/blob/main/CONTRIBUTING.md). The paper is in "
                f"[`paper/`]({url}/tree/main/paper).\n\n"
                f"<!-- sorry: {key} -->\n")
        print(f"  open   {title}")
        if apply:
            cmd = ["gh", "issue", "create", "--title", title, "--body", body, "--label", "proof"]
            if chapter_label(s["path"]):
                cmd += ["--label", chapter_label(s["path"])]
            r = run(cmd)
            print("        ", (r.stdout or r.stderr).strip())
            time.sleep(1.5)   # stay under GitHub's limit on creating content
    for key in stale:
        print(f"  close  #{open_issues[key]}  {key}")
        if apply:
            run(["gh", "issue", "close", str(open_issues[key]), "--comment",
                 f"`{key.split('::')[1]}` is no longer a `sorry` on main at {sha}."])
    ready = unblock(apply)
    if not apply and (new or stale or ready):
        print("dry run; pass --apply to make these changes")


def unblock(apply):
    """Remove `blocked` from open issues whose `<!-- needs: ... -->` issues are all closed."""
    states = {i["number"]: i["state"] for i in list_issues("all", "section")}
    blocked = list_issues("open", "blocked")
    ready = []
    for issue in sorted(blocked, key=lambda i: i["number"]):
        m = re.search(r"<!-- needs:([\d\s]*)-->", issue["body"] or "")
        if m and all(states.get(int(n)) == "closed" for n in m.group(1).split()):
            ready.append(issue["number"])
            print(f"  unblock #{issue['number']}  {issue['title']}")
            if apply:
                run(["gh", "issue", "edit", str(issue["number"]), "--remove-label", "blocked"])
    return ready


if __name__ == "__main__":
    main()
