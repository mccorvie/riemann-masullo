#!/usr/bin/env python3
"""Fail Main state when a statement that main had at its previous saved signatures has changed.

    scripts/ci/main_statements.py --target SHA [--previous-sha SHA] [--from-scratch]
        [--accept-baseline SHA --accept-target SHA --accept-names NAMES] PREVIOUS NEW

PREVIOUS and NEW are signature dumps (scripts/signatures.sh --all): the one Main state last saved,
for the commit `--previous-sha` (base_state.py --signatures), and the one just made at `--target`.
Every declaration of PREVIOUS must be in NEW with the same statement, apart from names beginning
`_private.`, as in the pull request check (verdict.statement_changes); new declarations are fine.

Neither dump may have a malformed line or be empty: a partly unreadable baseline would certify
only what survives (the pull request check refuses one too, #6287), and a malformed new dump
would become the next baseline. When there is no previous dump, or it is malformed, nothing can
be compared: that fails, except in a build from scratch (`--from-scratch`: the nightly, a run
with `full`, or one that found no saved build), which starts a new baseline and says so in the
summary. So a lost baseline stops merging until the next nightly at most, and an integrator can
restart it at once. (Main state does not pass `--from-scratch` when the download of the
signatures failed: only their absence starts a new baseline.)

The pull request check compares a pull request with the commit of main it was checked against,
which may be older than main's tip (#6414); this catches, within one build of main, a statement
that changed through what was merged meanwhile. A run that fails here uploads nothing, so the
next run compares with the same previous dump and fails again, and Auto-merge merges nothing
while it is red. When statements were changed on purpose, the integrator accepts exactly what
was reviewed: the three `--accept-*` options name the baseline commit and the target commit the
failed run showed, and the names (separated by spaces or commas). They apply only when both
commits are those of this run, and then only to the names listed: any other change still fails.
The run's summary lists every change, accepted or not, before anything is uploaded.

Exit status: 0 if nothing changed or everything that did was accepted, 1 otherwise.
"""
import argparse
import os
import re
import shlex
import sys
from pathlib import Path

import verdict

SHA = re.compile(r"[0-9a-f]{40}")


def problems(text):
    """Why a dump cannot be used: no declarations, or lines that are not signatures."""
    lines = [line for line in text.split("\n") if line]
    bad = [line for line in lines if not verdict.SIGNATURE_LINE.fullmatch(line)]
    if not lines:
        return ["it lists no declarations"]
    if bad:
        return [f"{len(bad)} malformed lines, the first: {bad[0][:200]!r}"]
    return []


def check(args):
    """(the lines of the report, whether it passed)."""
    new_text = Path(args.new).read_text()
    if why := problems(new_text):
        return [f"The new signature dump cannot be used: {why[0]}."], False
    previous = Path(args.previous)
    old_text = previous.read_text() if args.previous_sha and previous.is_file() else ""
    why = problems(old_text) if old_text else ["there are no saved signatures of main to compare with"]
    if why:
        lines = [f"The previous signatures ({(args.previous_sha or 'none')[:12]}) cannot be compared with: {why[0]}."]
        if args.from_scratch:
            return lines + ["Built from scratch, so these signatures start a new baseline; "
                            "nothing was compared."], True
        return lines + ["A build from scratch starts a new baseline: the nightly one, or "
                        "`gh workflow run main_state.yml --ref main -f full=true`."], False

    changed, removed, _private, _added, _bad = verdict.statement_changes(old_text, new_text)
    found = [(n, "changed") for n in changed] + [(n, "removed") for n in removed]
    span = f"`{args.previous_sha}`..`{args.target}`"
    if not found:
        return [f"No existing statement changed between the saved signatures and this commit ({span})."], True

    names = set(filter(None, re.split(r"[\s,]+", args.accept_names or "")))
    asked = bool(args.accept_baseline or args.accept_target or names)
    applies = asked and args.accept_baseline == args.previous_sha and args.accept_target == args.target
    lines = [f"Statements changed between the saved signatures and this commit ({span}):", ""]
    lines += [f"- `{n}` {how}" + (" (accepted)" if applies and n in names else "") for n, how in found]
    lines.append("")
    if asked and not applies:
        lines.append(f"The acceptance given was for `{args.accept_baseline}`..`{args.accept_target}`, not for "
                     "this run's commits, so it does not apply.")
    rest = [n for n, _ in found if not (applies and n in names)]
    if not rest:
        if unused := sorted(names - {n for n, _ in found}):
            lines.append("Listed but not changed: " + ", ".join(unused))
        return lines + ["Every change was accepted (accept_names)."], True
    full = " -f full=true" if args.from_scratch else ""
    lines += ["Not accepted: " + ", ".join(rest), "",
              "If these were intended, accept exactly them (prompts/integrator.md):", "",
              f"    gh workflow run main_state.yml --ref main{full} -f accept_baseline={args.previous_sha} "
              f"-f accept_target={args.target} -f accept_names={shlex.quote(' '.join(n for n, _ in found))}"]
    return lines, False


def main(argv):
    parser = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    parser.add_argument("previous")
    parser.add_argument("new")
    parser.add_argument("--target", required=True)
    parser.add_argument("--previous-sha", default="")
    parser.add_argument("--from-scratch", action="store_true")
    parser.add_argument("--accept-baseline", default="")
    parser.add_argument("--accept-target", default="")
    parser.add_argument("--accept-names", default="")
    args = parser.parse_args(argv)
    if not SHA.fullmatch(args.target) or (args.previous_sha and not SHA.fullmatch(args.previous_sha)):
        raise SystemExit("--target and --previous-sha must be full commit ids")
    lines, passed = check(args)
    for line in lines:
        print(line)
    summary = os.environ.get("GITHUB_STEP_SUMMARY")
    if summary:
        with open(summary, "a") as out:
            out.write("\n".join(lines) + "\n\n")
    return 0 if passed else 1


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
