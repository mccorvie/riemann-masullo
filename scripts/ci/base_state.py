#!/usr/bin/env python3
"""Start a pull request check from the build of main that the Main state workflow saved.

    scripts/ci/base_state.py --work DIR --base SHA --out DIR [--artifact ID]
    scripts/ci/base_state.py --choose --work DIR --main SHA --head SHA
    scripts/ci/base_state.py --signatures --work DIR --base SHA --out DIR

The first form unpacks the build directory of a `main-state` artifact into DIR/.lake/build and,
when it is for exactly `--base`, writes its signatures to `--out`/signatures-SHA.txt. The artifact
is `--artifact` if given (it must pass the same tests as below and be for `--base` or one of its
ancestors), otherwise the one for the newest ancestor of `--base` (itself included) by history,
as the second form ranks them (`newest`), not the newest upload. The build is unpacked next to DIR/.lake/build and moved into place only once it
is complete, so a failure leaves no partial build behind. Building main from scratch gives the
same result; this only saves the time.

The second form says which commit of main a pull request is checked against (#6414). It prints
that commit and the id of the saved build to start from ("-" if there is none). Let S be the
newest commit of main with a saved build, T main's tip (`--main`) and F the merge base of T and
the pull request. The check is against S, so that only the pull request is compiled and not
everything merged since S, when all of these hold (`usable_base`); otherwise against T:

  - F is S or an ancestor of it: the pull request contains no commit of main newer than S, so
    its own changes (F..head) are the same whichever of S and T they are measured from, and an
    ordinary merge into S uses the same merge base as one into T;
  - main has moved by at most MAX_SAVED_BEHIND commits since S, and the first of them is less
    than MAX_SAVED_AGE_HOURS old;
  - between S and T, main has changed none of the pull request's files and nothing that matters
    to every check (`matters_to_everyone`), and fewer than MAX_MOVED_FILES files.

The last two are `stale`, the same predicate Auto-merge applies between the checked commit and
main when it merges, with the larger bound MAX_BEHIND. So whenever Auto-merge asks for another
check because main has moved, the new check is never against the same commit again.

What main merged between S and T touches none of the pull request's files, but it can still
interact with them (an import that closes a cycle, an instance that changes how a statement
elaborates). The bounds keep that window comparable to the one between a check and its merge,
and two things in the workflows catch the rest within one build of main: Main state fails when a
statement existing at its previous saved build has changed (main_statements.py), and Auto-merge
merges nothing while the newest decisive Main state run has failed. A check against S that does
not come back `merge` or `read` is run again against T in the same run (pr_check.yml), so a pull
request is never told it fails because of the older base.

Both forms need GH_TOKEN (read access is enough), GH_REPO and REPO_ID, the numeric id of this
repository. DIR is a checkout with the history of main and the pull request's commit.

Only an artifact uploaded by a run on this repository's own `main` branch is used. A pull
request can upload an artifact with any name, but its run belongs to its own branch (and, from a
fork, to another repository), and GitHub records that, not the pull request. The Actions cache
is deliberately not used for this: a pull request can save a cache under any key, and later
runs of the same pull request would restore it in preference to main's.

The third form is for Main state's statement comparison (main_statements.py). It writes the
signatures Main state last saved, for the newest ancestor of `--base` by history (`newest`
again), to `--out`/previous-signatures.txt and their commit to `--out`/previous-signatures.sha,
and nothing when there are none. They come from the small `main-signatures` artifact, kept for
14 days (main_state.yml), not from the bulky `main-state` one, which is kept for
a day: a baseline must outlive a day of failed builds.

This file also holds what decides whether a change on main matters to a verdict, which
auto_merge.py imports: being under scripts/ci/, a change to it puts every verdict out of date.
"""
import argparse
import json
import os
import re
import shutil
import subprocess
import sys
import time
import zipfile
from pathlib import Path

import plain_proof

SHA = re.compile(r"[0-9a-f]{40}")
MAX_BYTES = 2 * 1024 ** 3
# How far main may have moved past the commit a verdict was computed against. MAX_BEHIND is
# Auto-merge's, when it merges. MAX_SAVED_BEHIND and MAX_SAVED_AGE_HOURS are the chooser's, when
# the check starts: main merges about 30 pull requests an hour and Main state saves a build every
# 30 to 90 minutes, so a saved build is normally under 40 commits and an hour or two behind; one
# further behind means Main state is failing or stuck, and the tip is used. A check against S
# takes some 20 minutes, so S is then at most about 50 commits behind main when Auto-merge acts:
# the old flow had about as many between its check's start and the merge (a check of the tip
# took 70 to 80 minutes). MAX_SAVED_BEHIND < MAX_BEHIND is what makes a check run again by
# Auto-merge for being too far behind choose a newer base.
MAX_BEHIND = 60
MAX_SAVED_BEHIND = 40
MAX_SAVED_AGE_HOURS = 3
MAX_MOVED_FILES = 300     # GitHub lists at most 300 files of a comparison
# Changes on main that make a verdict stale whatever files the pull request touches.
# Of scripts/, only what the check itself runs: a change to the launcher or to the integrator's
# tools does not touch any verdict, and counting it made every pending verdict stale.
BUILD_FILES = ("lakefile.toml", "lakefile.lean", "lean-toolchain", "lake-manifest.json", ".gitattributes",
               "scripts/lint.sh", "scripts/proof_review.sh", "scripts/signatures.sh", "scripts/Signatures.lean")
BUILD_DIRS = ("scripts/ci/", ".github/workflows/", "RiemannMasullo/External/")
# These files are independent of proof checking. The merge step applies its current policy
# to the completed check, whose verdict was produced by the separate PR check workflow.
NON_BUILD_FILES = (
    "RiemannMasullo/External/ATTRIBUTION.md",
    ".github/workflows/claims.yml",
    "scripts/ci/stale_claims.py",
    "scripts/ci/test_stale_claims.py",
    "scripts/ci/auto_merge.py",
    "scripts/ci/test_auto_merge.py",
)


def matters_to_everyone(path):
    """Whether a change to this file on main can change the result of any pull request's check."""
    if path in NON_BUILD_FILES:
        return False
    if path in BUILD_FILES or path.startswith(BUILD_DIRS) or path.endswith("/.gitattributes"):
        return True
    return path.endswith(".lean") and not plain_proof.library_file(path)


def stale(behind, moved, ours, limit):
    """Why a verdict about a pull request changing the files `ours` is out of date, or None, when
    main has since moved by `behind` commits that changed the files `moved` (both names of a
    rename). Used by the chooser here and by Auto-merge, with their own `limit`."""
    if behind > limit:
        return f"main has moved by {behind} commits since the commit checked against"
    if len(moved) >= MAX_MOVED_FILES:
        return "main has changed too many files since the commit checked against to tell"
    for path in moved:
        if path in ours:
            return f"main has since changed {path}, which this pull request also changes"
        if matters_to_everyone(path):
            return f"main has since changed {path}, which affects every check"
    return None


def usable(artifact, repo_id, name="main-state"):
    """The commit a `main-state` (or `name`) artifact is for, if it may be used, or None."""
    run = artifact.get("workflow_run") or {}
    sha = str(run.get("head_sha"))
    if (artifact.get("name") != name or artifact.get("expired") or run.get("repository_id") != repo_id
            or run.get("head_repository_id") != repo_id or run.get("head_branch") != "main"
            or not SHA.fullmatch(sha) or artifact.get("size_in_bytes", MAX_BYTES + 1) > MAX_BYTES):
        return None
    return sha


def api(repo, path):
    return json.loads(subprocess.run(["gh", "api", f"repos/{repo}/{path}"], check=True, capture_output=True).stdout)


def saved_builds(repo, repo_id, name="main-state"):
    """[(artifact, commit)] of the usable `main-state` (or `name`) artifacts, newest first."""
    listing = api(repo, f"actions/artifacts?name={name}&per_page=50")
    found = []
    for artifact in sorted(listing["artifacts"], key=lambda a: a["created_at"], reverse=True):
        sha = usable(artifact, repo_id, name)
        if sha:
            found.append((artifact, sha))
    return found


def git(work, *args):
    return subprocess.run(["git", "-c", "core.fsmonitor=false", *args], cwd=work, stdin=subprocess.DEVNULL,
                          capture_output=True, text=True)


def is_ancestor(work, older, newer):
    return git(work, "merge-base", "--is-ancestor", older, newer).returncode == 0


def usable_base(work, saved, main, head, now):
    """Why `head` must not be checked against `saved`, an ancestor of `main`, or None."""
    fork = git(work, "merge-base", main, head)
    if fork.returncode:
        return "the pull request shares no history with main"
    if not is_ancestor(work, fork.stdout.strip(), saved):
        return "the pull request contains commits of main newer than the saved build"
    listed = git(work, "diff", "--name-only", "-z", "--no-renames", fork.stdout.strip(), head)
    moved = git(work, "diff", "--name-only", "-z", "--no-renames", saved, main)
    times = git(work, "log", "--format=%ct", f"{saved}..{main}")
    if listed.returncode or moved.returncode or times.returncode:
        return "could not compare the saved build with main's tip"
    times = [int(t) for t in times.stdout.split()]
    why = stale(len(times), list(filter(None, moved.stdout.split("\0"))),
                set(filter(None, listed.stdout.split("\0"))), MAX_SAVED_BEHIND)
    if why:
        return why
    if times and now - min(times) > MAX_SAVED_AGE_HOURS * 3600:
        return f"main has differed from the saved build for more than {MAX_SAVED_AGE_HOURS} hours"
    return None


def newest(work, saved, tip):
    """The (artifact, commit) of [(artifact, commit)], newest upload first, whose commit is the
    newest ancestor of `tip` (itself included) by history, the newest upload among several for it;
    or None. A build of an older commit uploaded late does not displace it."""
    best = None
    for artifact, sha in saved:
        if is_ancestor(work, sha, tip) and (best is None or (sha != best[1] and is_ancestor(work, best[1], sha))):
            best = (artifact, sha)
    return best


def choose(work, main, head, saved, now=None):
    """(the commit to check `head` against, the saved build to start from or None, why), given
    [(artifact, commit)] of the saved builds, newest first."""
    best = newest(work, saved, main)
    if best is None:
        return main, None, "no saved build of main to check against: checking against main's tip"
    artifact, sha = best
    if sha == main:
        return main, artifact, "main's tip has a saved build"
    why = usable_base(work, sha, main, head, time.time() if now is None else now)
    if why:
        return main, artifact, f"{why} ({sha[:12]}): checking against main's tip"
    behind = git(work, "rev-list", "--count", f"{sha}..{main}").stdout.strip()
    return sha, artifact, f"checking against the saved build of main at {sha[:12]}, {behind} commits behind main's tip"


def restore(work, base, out, repo, repo_id, pinned=None):
    """Unpack a saved build into work/.lake/build (see the module's docstring)."""
    if pinned is not None:
        artifact = api(repo, f"actions/artifacts/{pinned}")
        sha = usable(artifact, repo_id)
        if not sha or not is_ancestor(work, sha, base):
            raise SystemExit(f"artifact {pinned} is not a saved build of {base[:12]} or an ancestor of it")
        chosen = (artifact, sha)
    else:
        chosen = newest(work, saved_builds(repo, repo_id), base)
    if not chosen:
        print("no saved state of main to start from; main will be built here")
        return
    artifact, sha = chosen
    archive = out / "main-state.zip"
    with open(archive, "wb") as target:
        subprocess.run(["gh", "api", f"repos/{repo}/actions/artifacts/{artifact['id']}/zip"],
                       check=True, stdout=target)
    with zipfile.ZipFile(archive) as bundle:
        for name in ("meta.json", "signatures.txt", "build.tar.zst"):
            with bundle.open(name) as source, open(out / name, "wb") as target:
                shutil.copyfileobj(source, target)
    archive.unlink()
    if json.loads((out / "meta.json").read_text()).get("sha") != sha:
        print("the saved state does not say which commit it is for; ignored")
        return
    lake = work / ".lake"
    staging = lake / "build.unpacking"
    shutil.rmtree(staging, ignore_errors=True)
    staging.mkdir(parents=True)
    try:
        subprocess.run(["tar", "-C", str(staging), "--no-same-owner", "-I", "zstd", "-xf",
                        str(out / "build.tar.zst")], check=True)
        if not (staging / "build").is_dir():
            raise SystemExit("the saved build has no build directory")
        shutil.rmtree(lake / "build", ignore_errors=True)
        (staging / "build").rename(lake / "build")
    finally:
        shutil.rmtree(staging, ignore_errors=True)
        (out / "build.tar.zst").unlink()
    if sha == base:
        (out / "signatures.txt").rename(out / f"signatures-{sha}.txt")
        print(f"starting from the saved build and signatures of main at {sha[:12]}")
    else:
        print(f"starting from the saved build of main at {sha[:12]}, an ancestor of {base[:12]}")


def previous_signatures(work, base, out, repo, repo_id):
    """Write the signatures Main state last saved for an ancestor of `base` (see the module's
    docstring); return their commit, or None."""
    chosen = newest(work, saved_builds(repo, repo_id, "main-signatures"), base)
    if not chosen:
        print("no saved signatures of main to compare with")
        return None
    artifact, sha = chosen
    archive = out / "main-signatures.zip"
    with open(archive, "wb") as target:
        subprocess.run(["gh", "api", f"repos/{repo}/actions/artifacts/{artifact['id']}/zip"],
                       check=True, stdout=target)
    with zipfile.ZipFile(archive) as bundle:
        meta = json.loads(bundle.read("meta.json"))
        if meta.get("sha") != sha:
            raise SystemExit(f"artifact {artifact['id']} does not say it is for {sha[:12]}")
        with bundle.open("signatures.txt") as source, open(out / "previous-signatures.txt", "wb") as target:
            shutil.copyfileobj(source, target)
    archive.unlink()
    (out / "previous-signatures.sha").write_text(sha + "\n")
    print(f"comparing with the signatures saved for main at {sha[:12]} (artifact {artifact['id']})")
    return sha


def main():
    parser = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    parser.add_argument("--work", required=True)
    parser.add_argument("--base")
    parser.add_argument("--out")
    parser.add_argument("--artifact", type=int)
    parser.add_argument("--choose", action="store_true")
    parser.add_argument("--signatures", action="store_true")
    parser.add_argument("--main")
    parser.add_argument("--head")
    args = parser.parse_args()
    repo, repo_id = os.environ["GH_REPO"], int(os.environ["REPO_ID"])
    work = Path(args.work)

    if args.choose:
        if not (args.main and args.head and SHA.fullmatch(args.main) and SHA.fullmatch(args.head)):
            raise SystemExit("--choose needs --main and --head, full commit ids")
        try:
            saved = saved_builds(repo, repo_id)
        except (subprocess.CalledProcessError, ValueError, KeyError):
            saved = []
        base, artifact, why = choose(work, args.main, args.head, saved)
        print(why, file=sys.stderr)
        print(base, artifact["id"] if artifact else "-")
        return 0

    if not (args.base and args.out and SHA.fullmatch(args.base)):
        raise SystemExit("--base (a full commit id) and --out are required")
    out = Path(args.out)
    out.mkdir(parents=True, exist_ok=True)
    if args.signatures:
        previous_signatures(work, args.base, out, repo, repo_id)
        return 0
    restore(work, args.base, out, repo, repo_id, args.artifact)
    return 0


if __name__ == "__main__":
    sys.exit(main())
