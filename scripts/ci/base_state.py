#!/usr/bin/env python3
"""Start a pull request check from the build of main that the Main state workflow saved.

    scripts/ci/base_state.py --work DIR --base SHA --out DIR
    scripts/ci/base_state.py --has-exact --base SHA

Looks for the newest ancestor `main-state` artifact by git history (newest upload among
several for the same commit), unpacks its build directory into DIR/.lake/build and, when it is
for exactly `--base`, writes its signatures to `--out`/signatures-SHA.txt. Building main from
scratch gives the same result; this only saves the time. It needs GH_TOKEN (read access is
enough), GH_REPO and REPO_ID, the numeric id of this repository.

With `--has-exact`, exits 0 iff a usable `main-state` artifact already exists for `--base`
(used by staggered scheduled Main state slots to skip cleanly when main has not moved).

Only an artifact uploaded by a run on this repository's own `main` branch is used. A pull
request can upload an artifact with any name, but its run belongs to its own branch (and, from a
fork, to another repository), and GitHub records that, not the pull request. The Actions cache
is deliberately not used for this: a pull request can save a cache under any key, and later
runs of the same pull request would restore it in preference to main's.
"""
import argparse
import json
import os
import re
import shutil
import subprocess
import sys
import zipfile
from pathlib import Path

SHA = re.compile(r"[0-9a-f]{40}")
MAX_BYTES = 2 * 1024 ** 3


def usable(artifact, repo_id, name="main-state"):
    """The commit a `main-state` artifact is for if it may be used, or None."""
    run = artifact.get("workflow_run") or {}
    sha = str(run.get("head_sha"))
    if (artifact.get("name") != name or artifact.get("expired") or run.get("repository_id") != repo_id
            or run.get("head_repository_id") != repo_id or run.get("head_branch") != "main"
            or not SHA.fullmatch(sha) or artifact.get("size_in_bytes", MAX_BYTES + 1) > MAX_BYTES):
        return None
    return sha


def saved_builds(repo, repo_id, name="main-state"):
    """[(artifact, commit)] of usable `main-state` artifacts, newest upload first."""
    listing = json.loads(subprocess.run(
        ["gh", "api", f"repos/{repo}/actions/artifacts?name={name}&per_page=100"],
        check=True, capture_output=True).stdout)
    found = []
    for artifact in sorted(listing["artifacts"], key=lambda a: a["created_at"], reverse=True):
        sha = usable(artifact, repo_id, name)
        if sha:
            found.append((artifact, sha))
    return found


def is_ancestor(work, older, newer):
    return subprocess.run(["git", "-c", "core.fsmonitor=false", "merge-base", "--is-ancestor", older, newer],
                          cwd=work, stdin=subprocess.DEVNULL).returncode == 0


def newest(work, saved, base):
    """The (artifact, commit) whose commit is the newest ancestor of `base` by git history,
    breaking ties in favor of the newest upload (as ordered in `saved`)."""
    best = None
    for artifact, sha in saved:
        if is_ancestor(work, sha, base) and (
                best is None or (sha != best[1] and is_ancestor(work, best[1], sha))):
            best = (artifact, sha)
    return best


def main():
    parser = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    parser.add_argument("--work")
    parser.add_argument("--base", required=True)
    parser.add_argument("--out")
    parser.add_argument("--has-exact", action="store_true")
    args = parser.parse_args()
    if not SHA.fullmatch(args.base):
        raise SystemExit("--base must be a full commit id")
    repo, repo_id = os.environ["GH_REPO"], int(os.environ["REPO_ID"])

    if args.has_exact:
        for artifact, sha in saved_builds(repo, repo_id):
            if sha == args.base:
                print(f"saved: {artifact['id']}")
                return 0
        return 1

    if not (args.work and args.out):
        raise SystemExit("--work and --out are required")
    work, out = Path(args.work), Path(args.out)
    out.mkdir(parents=True, exist_ok=True)

    chosen = newest(work, saved_builds(repo, repo_id), args.base)
    if not chosen:
        print("no saved state of main to start from; main will be built here")
        return 0
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
        return 0
    build = work / ".lake/build"
    shutil.rmtree(build, ignore_errors=True)
    (work / ".lake").mkdir(exist_ok=True)
    subprocess.run(["tar", "-C", str(work / ".lake"), "--no-same-owner", "-I", "zstd", "-xf",
                    str(out / "build.tar.zst")], check=True)
    (out / "build.tar.zst").unlink()
    if sha == args.base:
        (out / "signatures.txt").rename(out / f"signatures-{sha}.txt")
        print(f"starting from the saved build and signatures of main at {sha[:12]}")
    else:
        print(f"starting from the saved build of main at {sha[:12]}, an ancestor of {args.base[:12]}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
