#!/usr/bin/env python3
"""Merge the pull requests whose check said `merge`. Run by .github/workflows/auto_merge.yml.

    scripts/ci/auto_merge.py [--dry-run] [--retry-errors]
    scripts/ci/auto_merge.py --check BASE_SHA HEAD_SHA      what the merge step would conclude
                                                            for these two commits; changes nothing

This runs with a token that can write to the repository, so it never checks out, builds or
executes anything from a pull request, and it believes nothing a pull request could have forged.
The check (.github/workflows/pr_check.yml, scripts/ci/verdict.py) runs with a read-only token on
code from anywhere; all it hands over is an artifact named `verdict-merge` holding a small JSON
file. A pull request can change its own copy of that workflow and upload whatever it likes, so
the artifact is only a hint that a pull request is worth looking at. For each one, working from
commit ids and the GitHub API alone, this script

  1. finds the open pull request whose head is the commit the run was for, and requires the run
     to be the latest run of the check for that commit, finished and successful;
  2. reads the JSON (size-limited, never unpacked to disk) and takes two things from it: the
     verdict, which must be `merge`, and the commit of main it was computed against;
  3. compares the trees of the head commit and of its merge base with main, itself: every path
     that differs must be an existing, ordinary Lean file of the library. That rules out any
     change to the workflows, the scripts, the lakefile, the toolchain or the manifest, and so
     establishes that the run used main's checker and not the pull request's;
  4. fetches both versions of each changed file and repeats the text checks of the verdict
     (plain_proof.py and scripts/lint.sh, from main): plain proof text, no `sorry`, nothing that
     runs code at build time. With 3, a change that passes cannot have run code in the check,
     so the two things only the check can know (it builds, and no existing declaration
     changed) were reported by main's script and not by the pull request;
  5. requires that main has not moved, since the commit the verdict was computed against, in a
     way that matters to this pull request: no file it touches, nothing outside the library
     that affects the build, and at most MAX_BEHIND commits (base_state.stale, the predicate
     the check uses to choose that commit). If it has, the check is run again and nothing is
     merged; the new check is then never against the same commit (base_state.py). Nor may the
     pull request contain commits of main newer than that commit: its own changes are measured
     from its merge base with that commit, as the check measured them, and that is the merge
     base with main only then;
  6. squash-merges, naming the head commit, so that a push made after the check is not merged.

The check is usually against the newest commit of main with a saved build, not main's tip
(#6414), so nothing builds main's tip with the pull request before it is merged. Two things catch
what the merges in between do to it, within one build of main: Main state fails when an existing
statement has changed, and this script merges nothing while the line is stopped (`line_stopped`,
asked before the first and before every merge and every new check): while some Main state run on
main failed and no run created after it has succeeded on that commit or a later one. A failure
of a build from scratch is cleared only by a build from scratch, so that an incremental build
cannot hide it; and while a run is being run again, the line waits for it. Verdicts wait
meanwhile and are looked at again on every run of this workflow (every 15 minutes); the line
restarts after a push to main, the nightly build, a manual run or a re-run of the failed one,
once that succeeds. A verdict artifact expires after three days.

One run handles everything that is waiting, one pull request at a time (the workflow allows
only one run at once), so each merge is judged against a main that includes the previous one.
"""
import base64
import io
import json
import os
import re
import subprocess
import sys
import tempfile
import time
import urllib.parse
import zipfile
from pathlib import Path

import plain_proof
# What decides whether main has moved in a way that matters to a verdict is shared with the
# check's choice of the commit to check against (base_state.py), and lives there.
from base_state import BUILD_DIRS, BUILD_FILES, MAX_BEHIND, NON_BUILD_FILES, matters_to_everyone, stale  # noqa: F401

TOOLS = Path(__file__).resolve().parent.parent.parent
BRANCH = "main"
CHECK_WORKFLOW = ".github/workflows/pr_check.yml"
MAIN_WORKFLOW = "main_state.yml"
HOLD_LABEL = "integrator"     # what the merger puts on a pull request it leaves for the integrator
# What a check lane that merges pull requests in batches puts on those it is checking together,
# and on the others that change the same files: merging one of them alone in the meantime would
# make the batch's check useless. The lane removes the label when its check is over.
TRAIN_LABEL = "train"
SHA = re.compile(r"[0-9a-f]{40}")
REPO = re.compile(r"[A-Za-z0-9._-]+/[A-Za-z0-9._-]+")
MAX_ARTIFACT_BYTES = 256 * 1024
MAX_VERDICT_BYTES = 64 * 1024
MAX_FILES = 40            # changed files in one pull request
MAX_ATTEMPTS = 12         # runs of the check for one head commit
MAX_ERROR_ATTEMPTS = 3
MAX_MERGES = 60           # per run of this script
# Conclusions of a Main state run that say something about main; others (cancelled, skipped) do not.
DECISIVE = ("success", "failure", "timed_out", "startup_failure")
FROM_SCRATCH = "Main state, from scratch"     # the run name main_state.yml gives such a build


class LineStopped(Exception):
    """Main's build is broken: nothing more is merged or checked again in this run."""


class ApiError(Exception):
    def __init__(self, status, message):
        super().__init__(f"{status}: {message}")
        self.status, self.message = status, message


class Api:
    """The GitHub API through `gh`, with no shell and no values spliced into a command line."""

    def __init__(self, repo, dry_run=False):
        if not REPO.fullmatch(repo):
            raise SystemExit("GH_REPO must be owner/name")
        self.repo, self.dry_run, self.calls = repo, dry_run, 0

    def call(self, path, method="GET", body=None, binary=False):
        cmd = ["gh", "api", "--method", method, f"repos/{self.repo}/{path}".rstrip("/"),
               "-H", "X-GitHub-Api-Version: 2022-11-28"]
        if body is not None:
            cmd += ["--input", "-"]
        self.calls += 1
        done = subprocess.run(cmd, input=None if body is None else json.dumps(body).encode(),
                              capture_output=True)
        if done.returncode:
            stderr = done.stderr.decode("utf-8", "replace")
            code = re.search(r"\(HTTP (\d+)\)", stderr)
            try:
                message = str(json.loads(done.stdout).get("message", ""))
            except (ValueError, AttributeError):
                message = stderr
            raise ApiError(int(code.group(1)) if code else 0, message[:300])
        if binary:
            return done.stdout
        return json.loads(done.stdout) if done.stdout.strip() else None

    def change(self, what, path, method, body=None):
        """A call that changes something; only described when --dry-run."""
        if self.dry_run:
            print(f"  (dry run) would {what}")
            return {}
        return self.call(path, method, body)


def query(**params):
    return urllib.parse.urlencode(params)


def read_verdict(data):
    """The verdict JSON inside an artifact's zip, or None if it is not what verdict.py writes."""
    try:
        with zipfile.ZipFile(io.BytesIO(data)) as archive:
            info = archive.getinfo("verdict.json")
            if info.file_size > MAX_VERDICT_BYTES:
                return None
            with archive.open(info) as member:
                raw = member.read(MAX_VERDICT_BYTES + 1)
        if len(raw) > MAX_VERDICT_BYTES:
            return None
        verdict = json.loads(raw.decode("utf-8"))
    except (zipfile.BadZipFile, KeyError, ValueError, OSError, RuntimeError, NotImplementedError):
        return None
    if not isinstance(verdict, dict) or verdict.get("schema") != 1:
        return None
    if not all(isinstance(verdict.get(k), str) and SHA.fullmatch(verdict[k]) for k in ("head_sha", "base_sha")):
        return None
    if not isinstance(verdict.get("verdict"), str) or type(verdict.get("pr")) is not int:
        return None
    return verdict


class Merger:
    def __init__(self, api, retry_errors=False):
        self.api, self.retry_errors = api, retry_errors
        self.rows = []       # (pull request, commit, what happened)
        self.merged = 0
        self.scanner = plain_proof.Scanner()
        self.stopped = None  # why the line is stopped, if it is
        self.repo_id = None
        self.cleared = set() # ids of failed Main state runs a later success has cleared
        run_id = os.environ.get("GITHUB_RUN_ID", "")
        self.url = (f"{os.environ.get('GITHUB_SERVER_URL', 'https://github.com')}/{api.repo}/actions/runs/{run_id}"
                    if run_id.isdigit() else None)

    # -- what the pull request changes, from commit ids alone ---------------------------------

    def tree(self, sha):
        data = self.api.call(f"git/trees/{sha}?recursive=1")
        if data.get("truncated"):
            raise ApiError(0, "tree listing truncated")
        return {e["path"]: (e["mode"], e["type"], e["sha"]) for e in data["tree"] if e["type"] != "tree"}

    def blob(self, sha):
        data = self.api.call(f"git/blobs/{sha}")
        if data.get("size", MAX_ARTIFACT_BYTES * 100) > plain_proof.MAX_FILE_BYTES or data.get("encoding") != "base64":
            return None
        return base64.b64decode(data["content"])

    def merge_base(self, base, head):
        merge_base = self.api.call(f"compare/{base}...{head}?per_page=1")["merge_base_commit"]["sha"]
        if not SHA.fullmatch(merge_base):
            raise ApiError(0, "no merge base")
        return merge_base

    def rederive(self, base, head, merge_base=None):
        """(reasons the change is not a plain proof, the files it changes), from the API: what
        changed between `head` and its merge base with `base`, as the check measured it."""
        merge_base = merge_base or self.merge_base(base, head)
        before, after = self.tree(merge_base), self.tree(head)
        paths = sorted(p for p in set(before) | set(after) if before.get(p) != after.get(p))
        reasons = []
        if not paths:
            reasons.append("it changes no file")
        if len(paths) > MAX_FILES:
            return [f"it changes {len(paths)} files, more than is merged without a look"], paths
        for path in paths:
            old, new = before.get(path), after.get(path)
            if not plain_proof.library_file(path):
                reasons.append(f"{path!r} is not a Lean file of the library")
            elif old is None:
                reasons.append(f"new file {path}")
            elif new is None:
                reasons.append(f"deletes {path}")
            elif (old[0], old[1], new[0], new[1]) != ("100644", "blob", "100644", "blob"):
                reasons.append(f"{path} is not an ordinary file")
        if reasons:
            return reasons, paths
        with tempfile.TemporaryDirectory() as tmp:
            (Path(tmp) / "RiemannMasullo").mkdir()
            files = []
            for path in paths:
                old, new = self.blob(before[path][2]), self.blob(after[path][2])
                if old is None or new is None:
                    reasons.append(f"{path} is too large to check")
                    continue
                files.append((path, old, new))
                target = Path(tmp) / path      # `path` matched plain_proof.LIBRARY_FILE
                target.parent.mkdir(parents=True, exist_ok=True)
                target.write_bytes(new)
            reasons += plain_proof.classify_change(files, self.scanner)
            lint = subprocess.run([str(TOOLS / "scripts/lint.sh"), tmp], capture_output=True, stdin=subprocess.DEVNULL)
            if lint.returncode:
                reasons.append("the lint found a forbidden construct")
        return reasons, paths

    def since(self, base):
        """What main has done since `base`, or None if `base` is not a commit of main."""
        # The first page contains the change list for the whole comparison.
        ahead = self.api.call(f"compare/{base}...{BRANCH}?per_page=1")
        if ahead.get("status") not in ("identical", "ahead") or ahead.get("behind_by"):
            return None
        return ahead

    @staticmethod
    def moved(ahead, paths):
        """Why main has moved (see `since`) in a way that matters to a verdict about `paths`, or None."""
        if ahead["status"] == "identical":
            return None
        # GitHub lists at most 300 files; with as many names, `stale` says it cannot tell.
        if not isinstance(ahead.get("files"), list):
            return "GitHub did not list the files main changed since the check"
        names = [n for e in ahead["files"] for n in (e.get("filename"), e.get("previous_filename"))
                 if n is not None]
        return stale(ahead["ahead_by"], names, paths, MAX_BEHIND)

    def line_stopped(self, repo_id):
        """Why nothing may be merged now, or None. Among the latest 100 Main state runs on main:
        a run is being run again (its earlier attempt may have failed); or one failed and no run
        created after it succeeded on the same commit or a later one (a build from scratch, if
        the failed one was); or none has finished. One API call, and one per failure the first
        time it is found cleared by a success on another commit."""
        runs = self.api.call(f"actions/workflows/{MAIN_WORKFLOW}/runs?"
                             + query(branch=BRANCH, per_page=100))["workflow_runs"]
        ours = [r for r in runs if r.get("head_branch") == BRANCH and SHA.fullmatch(str(r.get("head_sha")))
                and r.get("event") in ("push", "schedule", "workflow_dispatch")
                and (r.get("repository") or {}).get("id") == repo_id
                and (r.get("head_repository") or {}).get("id") == repo_id]
        for run in ours:
            if run.get("status") != "completed" and run.get("run_attempt", 1) > 1:
                return f"a run of {MAIN_WORKFLOW} on main ({run.get('html_url') or run['id']}) is being run again"
        decisive = [r for r in ours if r.get("status") == "completed" and r.get("conclusion") in DECISIVE]
        if not decisive:
            return f"no run of {MAIN_WORKFLOW} on main has finished lately"
        def scratch(run):
            return run.get("event") == "schedule" or run.get("display_title") == FROM_SCRATCH
        when = lambda r: (r.get("created_at") or "", r["id"])
        successes = sorted((r for r in decisive if r["conclusion"] == "success"), key=when, reverse=True)
        for failed in sorted((r for r in decisive if r["conclusion"] != "success"), key=when, reverse=True):
            if failed["id"] in self.cleared:
                continue
            for success in successes:
                if when(success) <= when(failed) or (scratch(failed) and not scratch(success)):
                    continue
                if success["head_sha"] == failed["head_sha"] or self.api.call(
                        f"compare/{failed['head_sha']}...{success['head_sha']}?per_page=1").get("status") == "ahead":
                    self.cleared.add(failed["id"])
                    break
            else:
                return (f"a run of {MAIN_WORKFLOW} on main ({failed.get('html_url') or failed['id']}) ended in "
                        f"{failed['conclusion']}, and no later run on that commit or a newer one has succeeded"
                        + (" from scratch" if scratch(failed) else ""))
        return None

    def halt_if_stopped(self):
        """Ask again before a merge or a new check, since Main state may have failed meanwhile."""
        why = self.line_stopped(self.repo_id)
        if why:
            raise LineStopped(why)

    # -- acting -------------------------------------------------------------------------------

    def status(self, sha, state, text):
        body = dict(state=state, context="auto-merge", description=text[:140])
        if self.url:
            body["target_url"] = self.url
        try:
            self.api.change(f"set status {state}: {text}", f"statuses/{sha}", "POST", body)
        except ApiError as problem:
            print(f"  could not set the commit status: {problem}")

    def discard(self, artifact):
        try:
            self.api.change("delete the used verdict artifact", f"actions/artifacts/{artifact['id']}", "DELETE")
        except ApiError as problem:
            print(f"  could not delete artifact {artifact['id']}: {problem}")

    def check_again(self, run, artifact, sha, why, limit=MAX_ATTEMPTS):
        self.halt_if_stopped()
        if run.get("run_attempt", 1) >= limit:
            self.discard(artifact)
            self.status(sha, "error", f"Not merged automatically: {why}. Checked {limit} times; needs a person.")
            return f"given up after {limit} checks: {why}"
        # No commit status here: the check shows as running, and its new verdict replaces this one.
        self.api.change("run the check again", f"actions/runs/{run['id']}/rerun", "POST")
        self.discard(artifact)
        return f"checking again: {why}"

    def refuse(self, artifact, sha, why):
        self.discard(artifact)
        self.status(sha, "failure", f"Not merged automatically: {why}"[:140])
        print(f"::warning::verdict for {sha[:12]} said merge, but the merge step disagrees: {why[:200]}")
        return f"refused: {why}"

    def merge(self, number, sha):
        """True if merged; a string saying why not otherwise."""
        for wait in (0, 3, 8):
            time.sleep(wait)
            try:
                done = self.api.change(f"squash-merge #{number} at {sha[:12]}", f"pulls/{number}/merge", "PUT",
                                       dict(merge_method="squash", sha=sha))
                if self.api.dry_run or done.get("merged"):
                    return True
                return "GitHub did not merge it"
            except ApiError as problem:
                if problem.status == 403 and problem.message == "Resource not accessible by integration":
                    # The same workflow token can still merge another pull request.
                    return "the workflow token cannot merge this pull request (needs a project member)"
                if problem.status == 405 and "modified" in problem.message:
                    continue          # main moved under us; try again
                if problem.status == 409:
                    return "the branch was pushed to after the check"
                if problem.status not in (405, 422):
                    raise
                # Refused: because of a conflict with main, or because of a repository rule?
                state = self.api.call(f"pulls/{number}").get("mergeable_state")
                return "conflict" if state == "dirty" else f"GitHub refused the merge ({problem.message})"
        return "main kept moving"

    # -- one pull request ---------------------------------------------------------------------

    def latest_run(self, sha, head_repo):
        """The most recent run of the check for this commit."""
        runs = self.api.call("actions/runs?" + query(head_sha=sha, event="pull_request", per_page=50))
        ours = [r for r in runs["workflow_runs"]
                if r.get("path") == CHECK_WORKFLOW and r.get("event") == "pull_request"
                and r.get("head_sha") == sha and (r.get("head_repository") or {}).get("id") == head_repo]
        return max(ours, key=lambda r: (r.get("run_started_at") or "", r["id"])) if ours else None

    def handle(self, artifact, pr, repo_id):
        run_info = artifact["workflow_run"]
        sha, number = run_info["head_sha"], pr["number"]
        if run_info.get("repository_id") != repo_id:
            return "artifact of a run in another repository: ignored"
        if pr.get("draft"):
            return "draft: left alone"
        if HOLD_LABEL in [label["name"] for label in pr.get("labels", [])]:
            return f"labelled {HOLD_LABEL}: left alone"
        if TRAIN_LABEL in [label["name"] for label in pr.get("labels", [])]:
            return f"labelled {TRAIN_LABEL}: left to the batch it is being checked in"
        run = self.latest_run(sha, run_info["head_repository_id"])
        if run is None or run["id"] != run_info["id"]:
            if run is not None and run.get("status") == "completed":
                self.discard(artifact)
            return "a newer run of the check exists"
        if run.get("status") != "completed":
            return "the check is running again"
        if artifact["created_at"] < (run.get("run_started_at") or ""):
            self.discard(artifact)
            return "verdict from an earlier attempt: dropped"
        if artifact["name"] == "verdict-error":
            return self.check_again(run, artifact, sha, "the check could not be carried out", MAX_ERROR_ATTEMPTS)
        if run.get("conclusion") != "success":
            return self.refuse(artifact, sha, "the run that uploaded the verdict did not succeed")
        if artifact.get("size_in_bytes", MAX_ARTIFACT_BYTES + 1) > MAX_ARTIFACT_BYTES:
            return self.refuse(artifact, sha, "the verdict artifact is too large")
        verdict = read_verdict(self.api.call(f"actions/artifacts/{artifact['id']}/zip", binary=True))
        if verdict is None or verdict["verdict"] != "merge" or verdict["head_sha"] != sha or verdict["pr"] != number:
            return self.refuse(artifact, sha, "the verdict artifact is malformed or is about something else")
        base = verdict["base_sha"]

        # The pull request as it is now, not as the list a moment ago had it.
        pr = self.api.call(f"pulls/{number}")
        if (pr.get("state") != "open" or pr.get("draft") or pr["head"]["sha"] != sha
                or pr["base"]["ref"] != BRANCH or pr["base"]["repo"]["id"] != repo_id):
            return "the pull request changed meanwhile"

        # The commit the verdict names as main must be one: everything below is relative to it.
        ahead = self.since(base)
        if ahead is None:
            return self.refuse(artifact, sha, "the verdict was not computed against a commit of main")
        # Its own changes, measured from its merge base with that commit as the check measured
        # them, are what they would be against main only if that is also its merge base with main.
        merge_base = self.merge_base(base, sha)
        if self.merge_base(BRANCH, sha) != merge_base:
            return self.check_again(run, artifact, sha, "the pull request contains commits of main newer "
                                    "than the commit it was checked against")
        reasons, paths = self.rederive(base, sha, merge_base)
        if reasons:
            return self.refuse(artifact, sha, "; ".join(reasons)[:400])
        why = self.moved(ahead, set(paths))
        if why:
            return self.check_again(run, artifact, sha, why)
        self.halt_if_stopped()
        result = self.merge(number, sha)
        if result is True:
            self.merged += 1
            return "merged"
        if result == "conflict":
            return self.check_again(run, artifact, sha, "it no longer merges cleanly into main")
        if result.startswith("GitHub refused"):
            # A branch rule, most likely. Trying again will not help; someone has to look.
            self.discard(artifact)
            self.status(sha, "error", f"Not merged automatically: {result}")
            print(f"::warning::#{number}: {result[:200]}")
        return f"not merged: {result}"

    # -- everything that is waiting -----------------------------------------------------------

    def waiting(self):
        """Verdict artifacts to act on, oldest first: the newest per head commit and kind."""
        kinds = ["verdict-merge"] + (["verdict-error"] if self.retry_errors else [])
        found = []
        for kind in kinds:
            listing = self.api.call("actions/artifacts?" + query(name=kind, per_page=100))
            seen = set()
            for artifact in sorted(listing["artifacts"], key=lambda a: a["created_at"], reverse=True):
                run = artifact.get("workflow_run") or {}
                key = (run.get("head_repository_id"), run.get("head_branch"), run.get("head_sha"))
                if artifact.get("expired") or key in seen or not SHA.fullmatch(str(run.get("head_sha"))):
                    continue
                seen.add(key)
                found.append(artifact)
        return sorted(found, key=lambda a: a["created_at"])

    def open_pull_requests(self):
        prs, page = {}, 1
        while page <= 20:
            batch = self.api.call("pulls?" + query(state="open", base=BRANCH, per_page=100, page=page))
            for pr in batch:
                if pr["head"].get("repo"):
                    prs[(pr["head"]["repo"]["id"], pr["head"]["ref"], pr["head"]["sha"])] = pr
            if len(batch) < 100:
                break
            page += 1
        return prs

    def drain(self):
        artifacts = self.waiting()
        if not artifacts:
            print("nothing is waiting")
            return
        given = os.environ.get("GITHUB_REPOSITORY_ID", "")
        repo_id = int(given) if given.isdigit() else self.api.call("")["id"]
        self.repo_id = repo_id
        stopped = self.line_stopped(repo_id)
        if stopped:
            self.stopped = stopped
            print(f"::warning::nothing is merged while main's build is broken: {stopped}")
            return
        prs = self.open_pull_requests()
        for artifact in artifacts:
            run = artifact["workflow_run"]
            pr = prs.get((run["head_repository_id"], run["head_branch"], run["head_sha"]))
            if pr is None:
                continue          # merged, closed or pushed to since; the artifact expires by itself
            if self.merged >= MAX_MERGES:
                print("enough for one run; the rest waits for the next")
                break
            try:
                outcome = self.handle(artifact, pr, repo_id)
            except LineStopped as stopped:
                self.stopped = str(stopped)
                self.rows.append((pr["number"], run["head_sha"], "left waiting: main's build is broken"))
                print(f"::warning::nothing more is merged while main's build is broken: {stopped}")
                break
            except ApiError as problem:
                outcome = f"GitHub API error, left for the next run ({problem})"
                if problem.status in (401, 403, 429):
                    self.rows.append((pr["number"], run["head_sha"], outcome))
                    print(f"#{pr['number']} {run['head_sha'][:12]}: {outcome}")
                    print("::error::the token was refused or rate-limited; stopping")
                    break
            self.rows.append((pr["number"], run["head_sha"], outcome))
            print(f"#{pr['number']} {run['head_sha'][:12]}: {outcome}")
        if self.merged:
            # A merge made with the workflow token starts no `push` workflow, so ask for main's
            # build (and the signatures the next checks start from) explicitly.
            try:
                self.api.change("start the Main state workflow", f"actions/workflows/{MAIN_WORKFLOW}/dispatches",
                                "POST", dict(ref=BRANCH))
            except ApiError as problem:
                print(f"::warning::could not start {MAIN_WORKFLOW}: {problem}")

    def summary(self):
        target = os.environ.get("GITHUB_STEP_SUMMARY")
        if target and self.stopped:
            with open(target, "a") as out:
                out.write(f"Nothing merged: {self.stopped}.\n")
        if not target or not self.rows:
            return
        lines = ["| Pull request | Commit | Outcome |", "|---|---|---|"]
        for number, sha, outcome in self.rows:
            shown = re.sub(r"[^\x20-\x7e]", "?", outcome).replace("|", "/").replace("`", "'")[:300]
            lines.append(f"| #{number} | `{sha[:12]}` | {shown} |")
        with open(target, "a") as out:
            out.write("\n".join(lines) + "\n")


def main(argv):
    api = Api(os.environ.get("GH_REPO", ""), dry_run="--dry-run" in argv or "--check" in argv)
    merger = Merger(api, retry_errors="--retry-errors" in argv)
    if "--check" in argv:
        base, head = argv[argv.index("--check") + 1:][:2]
        if not (SHA.fullmatch(base) and SHA.fullmatch(head)):
            raise SystemExit("--check takes two full commit ids")
        reasons, paths = merger.rederive(base, head)
        print("files:", ", ".join(paths))
        print("plain proof:", "yes" if not reasons else "no")
        for reason in reasons:
            print("  " + reason)
        ahead = merger.since(base)
        print("main since the base:", "the base is not a commit of main" if ahead is None
              else merger.moved(ahead, set(paths)) or "nothing that matters")
        print(f"({api.calls} API calls)")
        return 0
    merger.drain()
    merger.summary()
    print(f"merged {merger.merged}; {api.calls} API calls")
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
