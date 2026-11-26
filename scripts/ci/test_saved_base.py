"""Checking a pull request against the newest saved build of main instead of main's tip (#6414):
which commit base_state.py chooses, and how verdict.py applies the pull request to it."""
import contextlib
import io
import json
import os
import re
import subprocess
import tempfile
import types
import unittest
import zipfile
from pathlib import Path
from unittest import mock

import auto_merge
import base_state
import main_statements
import verdict

A = "RiemannMasullo/AppA/Sec1.lean"
B = "RiemannMasullo/AppB/Sec2.lean"
PROOF_BEFORE = "theorem t : True := by\n  sorry\n"
PROOF_AFTER = "theorem t : True := by\n  trivial\n"


class Repo(unittest.TestCase):
    """main: saved -> other -> tip; a pull request on A, branched from `saved` or from `tip`."""

    def setUp(self):
        temp = tempfile.TemporaryDirectory()
        self.addCleanup(temp.cleanup)
        self.dir = Path(temp.name)
        self.env = dict(os.environ, GIT_AUTHOR_NAME="t", GIT_AUTHOR_EMAIL="t@invalid", GIT_COMMITTER_NAME="t",
                        GIT_COMMITTER_EMAIL="t@invalid", GIT_CONFIG_GLOBAL="/dev/null", GIT_CONFIG_NOSYSTEM="1")
        self.git("init", "-q", "-b", "main")
        self.saved = self.commit({A: PROOF_BEFORE, B: PROOF_BEFORE, "README.md": "x\n"})

    def git(self, *args):
        return subprocess.run(["git", *args], cwd=self.dir, env=self.env, check=True,
                              capture_output=True, text=True).stdout.strip()

    def commit(self, files):
        for path, text in files.items():
            target = self.dir / path
            target.parent.mkdir(parents=True, exist_ok=True)
            if text is None:
                target.unlink()
            else:
                target.write_text(text)
        self.git("add", "-A")
        self.git("commit", "-q", "-m", "c")
        return self.git("rev-parse", "HEAD")

    def branch(self, start, files):
        """A commit on top of `start` that is not on main; main's checkout is left as it was."""
        here = self.git("rev-parse", "HEAD")
        self.git("checkout", "-q", "--detach", start)
        sha = self.commit(files)
        self.git("checkout", "-q", "--detach", here)
        return sha

    def merge_main_into(self, head, main):
        here = self.git("rev-parse", "HEAD")
        self.git("checkout", "-q", "--detach", head)
        self.git("merge", "-q", "--no-edit", main)
        sha = self.git("rev-parse", "HEAD")
        self.git("checkout", "-q", "--detach", here)
        return sha


def saved(*shas):
    """[(artifact, commit)] as base_state.saved_builds lists them, newest upload first."""
    return [(dict(id=100 + i), sha) for i, sha in enumerate(shas)]


class Choose(Repo):
    def choose(self, main, head, builds, now=None):
        return base_state.choose(self.dir, main, head, saved(*builds), now)[0]

    def test_saved_build_when_main_changed_other_library_files(self):
        tip = self.commit({B: PROOF_AFTER, "README.md": "y\n"})
        head = self.branch(self.saved, {A: PROOF_AFTER})
        self.assertEqual(self.choose(tip, head, [self.saved]), self.saved)

    def test_the_saved_build_that_was_validated_is_named(self):
        middle = self.commit({B: PROOF_AFTER})
        tip = self.commit({"README.md": "y\n"})
        head = self.branch(self.saved, {A: PROOF_AFTER})
        self.assertEqual(base_state.choose(self.dir, tip, head, saved(self.saved, middle))[:2], (middle, dict(id=101)))
        # against the tip too, the build to start from is the one the choice was made with
        head = self.branch(tip, {A: PROOF_AFTER})
        self.assertEqual(base_state.choose(self.dir, tip, head, saved(self.saved, middle))[:2], (tip, dict(id=101)))
        self.assertEqual(base_state.choose(self.dir, tip, head, [])[:2], (tip, None))

    def test_tip_when_the_pull_request_contains_newer_commits_of_main(self):
        # Review of #6461, item 1: branched from (or merged) main after the saved build, it may
        # use what main merged since, in files it does not change.
        tip = self.commit({B: PROOF_AFTER, "README.md": "y\n"})
        cut_after = self.branch(tip, {A: PROOF_AFTER})
        merged_after = self.merge_main_into(self.branch(self.saved, {A: PROOF_AFTER}), tip)
        self.assertEqual(self.choose(tip, cut_after, [self.saved]), tip)
        self.assertEqual(self.choose(tip, merged_after, [self.saved]), tip)

    def test_tip_when_branched_from_a_version_main_later_reverted(self):
        middle = self.commit({A: PROOF_BEFORE + "-- for a while\n"})
        tip = self.commit({A: PROOF_BEFORE})                    # no net change between saved and tip
        head = self.branch(middle, {A: PROOF_AFTER + "-- for a while\n"})
        self.assertEqual(self.choose(tip, head, [self.saved]), tip)

    def test_saved_build_when_main_changed_the_file_before_it(self):
        # main changed A after the branch point but before the saved build: an ordinary merge
        # into the saved build, from the same merge base as into the tip
        start = self.saved
        self.saved = self.commit({A: "-- header\n" + PROOF_BEFORE})
        tip = self.commit({B: PROOF_AFTER})
        head = self.branch(start, {A: PROOF_AFTER})
        self.assertEqual(self.choose(tip, head, [self.saved]), self.saved)

    def test_tip_when_main_changed_a_file_of_the_pull_request(self):
        tip = self.commit({A: PROOF_BEFORE + "\n"})
        head = self.branch(self.saved, {A: PROOF_AFTER})
        self.assertEqual(self.choose(tip, head, [self.saved]), tip)

    def test_tip_when_main_changed_what_every_check_uses(self):
        for path in ("lakefile.toml", "scripts/ci/verdict.py", "scripts/ci/command_keywords.txt",
                     "scripts/ci/base_state.py", ".gitattributes", "RiemannMasullo/External/X.lean", "Main.lean"):
            tip = self.commit({path: "changed " + path})
            head = self.branch(self.saved, {A: PROOF_AFTER})
            self.assertEqual(self.choose(tip, head, [self.saved]), tip, path)
            self.saved = tip

    def test_tip_when_the_saved_build_is_too_far_behind(self):
        for i in range(base_state.MAX_SAVED_BEHIND):
            tip = self.commit({B: PROOF_BEFORE + "--\n" * (i + 1)})
        head = self.branch(self.saved, {A: PROOF_AFTER})
        self.assertEqual(self.choose(tip, head, [self.saved]), self.saved)
        tip = self.commit({B: PROOF_AFTER})
        self.assertEqual(self.choose(tip, head, [self.saved]), tip)

    def test_tip_when_main_has_differed_from_the_saved_build_too_long(self):
        tip = self.commit({B: PROOF_AFTER})
        head = self.branch(self.saved, {A: PROOF_AFTER})
        landed = int(self.git("log", "-1", "--format=%ct", tip))
        hours = base_state.MAX_SAVED_AGE_HOURS * 3600
        self.assertEqual(self.choose(tip, head, [self.saved], now=landed + hours - 60), self.saved)
        self.assertEqual(self.choose(tip, head, [self.saved], now=landed + hours + 60), tip)

    def test_newest_commit_with_a_build_whatever_the_upload_order(self):
        middle = self.commit({B: PROOF_AFTER})
        tip = self.commit({"README.md": "y\n"})
        head = self.branch(self.saved, {A: PROOF_AFTER})
        # a build from scratch of `saved` uploaded after the incremental one of `middle`
        self.assertEqual(self.choose(tip, head, [self.saved, middle]), middle)
        self.assertEqual(self.choose(tip, head, [middle, self.saved]), middle)

    def test_tip_without_a_usable_build(self):
        tip = self.commit({B: PROOF_AFTER})
        other = self.branch(self.saved, {"README.md": "elsewhere\n"})     # not a commit of main
        head = self.branch(self.saved, {A: PROOF_AFTER})
        self.assertEqual(self.choose(tip, head, []), tip)
        self.assertEqual(self.choose(tip, head, [other]), tip)
        self.assertEqual(self.choose(tip, head, [tip]), tip)


class SamePredicateAsAutoMerge(Repo):
    """Review of #6461, item 3: whenever Auto-merge runs a check again because main has moved, the
    chooser does not pick the commit that check was against again."""

    def test_bounds(self):
        self.assertLess(base_state.MAX_SAVED_BEHIND, auto_merge.MAX_BEHIND)
        self.assertIs(auto_merge.stale, base_state.stale)
        self.assertIs(auto_merge.matters_to_everyone, base_state.matters_to_everyone)

    def test_every_reason_to_check_again_is_a_reason_not_to_choose(self):
        for moved in ([B], [A], ["README.md"], ["lakefile.toml"], ["scripts/ci/plain_proof.py"],
                      [".gitattributes"], ["Main.lean"], ["scripts/review.sh"]):
            for behind in (1, auto_merge.MAX_BEHIND, auto_merge.MAX_BEHIND + 1):
                ahead = dict(status="ahead", ahead_by=behind, files=[dict(filename=f) for f in moved])
                merger = auto_merge.Merger.moved(ahead, {A})
                chooser = base_state.stale(behind, moved, {A}, base_state.MAX_SAVED_BEHIND)
                if merger:
                    self.assertTrue(chooser, (moved, behind))

    def test_through_git(self):
        for _ in range(auto_merge.MAX_BEHIND + 1):
            tip = self.commit({"README.md": self.git("rev-parse", "HEAD")})
        head = self.branch(self.saved, {A: PROOF_AFTER})
        ahead = dict(status="ahead", ahead_by=auto_merge.MAX_BEHIND + 1, files=[dict(filename="README.md")])
        self.assertTrue(auto_merge.Merger.moved(ahead, {A}))
        self.assertEqual(self.choose_base(tip, head), tip)

    def choose_base(self, tip, head):
        return base_state.choose(self.dir, tip, head, saved(self.saved))[0]


class ApplyToSavedBase(Repo):
    """verdict.Check with `--base` the saved build and `--main` the tip."""

    def check(self, base, head, main):
        self.git("checkout", "-q", "--detach", base)
        return verdict.Check(self.dir, base, head, main)

    def old_merge(self, tip, head, paths):
        """The old flow: an ordinary merge of the pull request into main's tip, in a scratch work tree."""
        scratch = self.dir / ".scratch"
        self.git("worktree", "add", "-q", "--detach", str(scratch), tip)
        try:
            subprocess.run(["git", "merge", "--no-commit", "--no-ff", head], cwd=scratch, env=self.env, check=True,
                           capture_output=True)
            return {p: (scratch / p).read_text() if (scratch / p).exists() else None for p in paths}
        finally:
            self.git("worktree", "remove", "--force", str(scratch))

    def assert_same_as_against_the_tip(self, base, head, tip):
        check = self.check(base, head, tip)
        entries = check.changed_files()
        files = [e["path"] for e in entries]
        check.merge(entries)
        everything = set(self.git("ls-files").split("\n")) | set(files)
        ours = {p: (self.dir / p).read_text() if (self.dir / p).exists() else None for p in everything}
        before = self.old_merge(tip, head, everything)
        for path in everything:
            if path in files:
                self.assertEqual(ours[path], before[path], path)       # the pull request's files: as before
            else:
                expected = self.git("show", f"{base}:{path}")
                self.assertEqual(ours[path].rstrip("\n"), expected, path)   # the rest: the saved base's
        return files

    def test_same_as_before_when_base_is_the_tip(self):
        tip = self.commit({B: PROOF_AFTER})
        head = self.branch(self.saved, {A: PROOF_AFTER})
        self.assertEqual(self.assert_same_as_against_the_tip(tip, head, tip), [A])

    def test_the_pull_requests_files_merge_as_into_the_tip(self):
        # main changed A before the saved build, after the branch point: a real three-way merge
        start = self.saved
        self.saved = self.commit({A: "-- header\n" + PROOF_BEFORE})
        tip = self.commit({B: PROOF_AFTER, "README.md": "y\n"})
        head = self.branch(start, {A: PROOF_AFTER, "RiemannMasullo/AppA/New.lean": "theorem n : True := trivial\n"})
        self.assertEqual(base_state.choose(self.dir, tip, head, saved(self.saved))[0], self.saved)
        files = self.assert_same_as_against_the_tip(self.saved, head, tip)
        self.assertEqual(sorted(files), sorted([A, "RiemannMasullo/AppA/New.lean"]))
        self.assertEqual((self.dir / A).read_text(), "-- header\n" + PROOF_AFTER)

    def test_refused_when_the_pull_request_contains_newer_commits_of_main(self):
        tip = self.commit({B: PROOF_AFTER})
        for head in (self.branch(tip, {A: PROOF_AFTER}), self.merge_main_into(self.branch(self.saved, {A: PROOF_AFTER}), tip)):
            with self.assertRaises(verdict.Stop) as stopped:
                self.check(self.saved, head, tip).changed_files()
            self.assertEqual(stopped.exception.verdict, "error")

    def test_refused_when_the_base_is_not_main(self):
        tip = self.commit({B: PROOF_AFTER})
        other = self.branch(self.saved, {"README.md": "elsewhere\n"})
        head = self.branch(self.saved, {A: PROOF_AFTER})
        with self.assertRaises(verdict.Stop) as stopped:
            self.check(other, head, tip).changed_files()
        self.assertEqual(stopped.exception.verdict, "error")


class Restore(Repo):
    """base_state.restore: the pinned saved build, unpacked whole or not at all (review item 6)."""

    REPO_ID = 7

    def artifact(self, sha, ident=55, **run):
        return dict(id=ident, name="main-state", expired=False, size_in_bytes=1000, created_at="2026-01-01T00:00:00Z",
                    workflow_run=dict(dict(repository_id=self.REPO_ID, head_repository_id=self.REPO_ID,
                                           head_branch="main", head_sha=sha), **run))

    def bundle(self, sha, tar_bytes=None):
        """The zip of a `main-state` artifact for `sha`, whose build holds one file."""
        if tar_bytes is None:
            src = self.dir / ".src"
            (src / "build/lib").mkdir(parents=True, exist_ok=True)
            (src / "build/lib/A.olean").write_text("olean")
            subprocess.run(["tar", "-C", str(src), "-I", "zstd", "-cf", str(self.dir / ".b.tar.zst"), "build"], check=True)
            tar_bytes = (self.dir / ".b.tar.zst").read_bytes()
        data = io.BytesIO()
        with zipfile.ZipFile(data, "w") as archive:
            archive.writestr("meta.json", json.dumps(dict(sha=sha)))
            archive.writestr("signatures.txt", "theorem t 1\n")
            archive.writestr("build.tar.zst", tar_bytes)
        return data.getvalue()

    def restore(self, base, pinned, artifacts, zips):
        real = subprocess.run
        def run(cmd, *args, **kwargs):
            if cmd[0] == "gh":
                ident = int(re.search(r"artifacts/(\d+)/zip", cmd[2]).group(1))
                kwargs["stdout"].write(zips[ident])
                return subprocess.CompletedProcess(cmd, 0)
            return real(cmd, *args, **kwargs)
        def api(_repo, path):
            if path.startswith("actions/artifacts?"):
                self.listed = True
                return dict(artifacts=list(artifacts.values()))
            return artifacts[int(path.rsplit("/", 1)[1])]
        self.listed = False
        out = self.dir / ".out"
        out.mkdir(exist_ok=True)
        with mock.patch.object(base_state, "api", api), mock.patch.object(base_state.subprocess, "run", run), \
                contextlib.redirect_stdout(io.StringIO()) as printed:
            base_state.restore(self.dir, base, out, "o/r", self.REPO_ID, pinned)
        self.printed = printed.getvalue()
        return out

    def test_the_pinned_build_is_used_without_listing_again(self):
        tip = self.commit({B: PROOF_AFTER})
        newer = self.artifact(tip, 56)     # listed now, but not the one the choice was made with
        out = self.restore(tip, 55, {55: self.artifact(self.saved), 56: newer},
                           {55: self.bundle(self.saved), 56: self.bundle(tip)})
        self.assertFalse(self.listed)
        self.assertEqual((self.dir / ".lake/build/lib/A.olean").read_text(), "olean")
        self.assertFalse((out / f"signatures-{tip}.txt").exists())          # an ancestor's build
        self.assertFalse((self.dir / ".lake/build.unpacking").exists())

    def test_a_pinned_artifact_that_is_not_main_s_is_refused(self):
        tip = self.commit({B: PROOF_AFTER})
        other = self.branch(self.saved, {"README.md": "elsewhere\n"})
        for artifact in (self.artifact(self.saved, head_branch="feature"), self.artifact(other),
                         self.artifact(self.saved, head_repository_id=99)):
            with self.assertRaises(SystemExit):
                self.restore(tip, 55, {55: artifact}, {55: self.bundle(artifact["workflow_run"]["head_sha"])})
            self.assertFalse((self.dir / ".lake/build").exists())

    def test_a_broken_archive_leaves_no_partial_build(self):
        (self.dir / ".lake/build").mkdir(parents=True)
        (self.dir / ".lake/build/old").write_text("kept")
        good = self.bundle(self.saved)
        tar_bytes = zipfile.ZipFile(io.BytesIO(good)).read("build.tar.zst")
        with self.assertRaises(subprocess.CalledProcessError):
            self.restore(self.saved, 55, {55: self.artifact(self.saved)},
                         {55: self.bundle(self.saved, tar_bytes[: len(tar_bytes) // 2])})
        self.assertEqual((self.dir / ".lake/build/old").read_text(), "kept")
        self.assertFalse((self.dir / ".lake/build.unpacking").exists())

    def test_unpinned_the_newest_by_history_not_the_newest_upload(self):
        # second review, item 4: a build from scratch of an older commit uploaded late
        middle = self.commit({B: PROOF_AFTER})
        tip = self.commit({"README.md": "y\n"})
        late = self.artifact(self.saved, 56, created_at="2026-01-02T00:00:00Z")
        out = self.restore(tip, None, {55: self.artifact(middle), 56: late},
                           {55: self.bundle(middle), 56: self.bundle(self.saved)})
        self.assertIn(f"saved build of main at {middle[:12]}", self.printed)
        self.assertFalse((out / f"signatures-{tip}.txt").exists())

    def signatures(self, base, artifacts, zips):
        real = subprocess.run
        def run(cmd, *args, **kwargs):
            if cmd[0] != "gh":
                return real(cmd, *args, **kwargs)
            ident = int(re.search(r"artifacts/(\d+)/zip", cmd[2]).group(1))
            kwargs["stdout"].write(zips[ident])
            return subprocess.CompletedProcess(cmd, 0)
        def api(_repo, path):
            self.assertIn("name=main-signatures", path)
            return dict(artifacts=artifacts)
        out = self.dir / ".sig"
        out.mkdir(exist_ok=True)
        with mock.patch.object(base_state, "api", api), mock.patch.object(base_state.subprocess, "run", run), \
                contextlib.redirect_stdout(io.StringIO()):
            return base_state.previous_signatures(self.dir, base, out, "o/r", self.REPO_ID), out

    def signatures_zip(self, sha, text):
        data = io.BytesIO()
        with zipfile.ZipFile(data, "w") as archive:
            archive.writestr("meta.json", json.dumps(dict(sha=sha)))
            archive.writestr("signatures.txt", text)
        return data.getvalue()

    def test_main_state_compares_with_the_newest_saved_signatures_by_history(self):
        # second review, items 1 and 4: kept apart from the build, ranked as the chooser ranks
        middle = self.commit({B: PROOF_AFTER})
        tip = self.commit({"README.md": "y\n"})
        artifacts = [dict(self.artifact(self.saved, 56, created_at="2026-01-02T00:00:00Z"), name="main-signatures"),
                     dict(self.artifact(middle, 55), name="main-signatures"),
                     self.artifact(tip, 57)]          # a `main-state` artifact: not a baseline
        sha, out = self.signatures(tip, artifacts, {55: self.signatures_zip(middle, "theorem m 1\n"),
                                                    56: self.signatures_zip(self.saved, "theorem s 1\n")})
        self.assertEqual(sha, middle)
        self.assertEqual((out / "previous-signatures.txt").read_text(), "theorem m 1\n")
        self.assertEqual((out / "previous-signatures.sha").read_text().strip(), middle)
        self.assertEqual(self.signatures(tip, [], {})[0], None)
        with self.assertRaises(SystemExit):        # an artifact whose contents name another commit
            self.signatures(tip, artifacts[1:2], {55: self.signatures_zip(self.saved, "theorem s 1\n")})

    def test_exact_build_brings_its_signatures(self):
        out = self.restore(self.saved, None, {55: self.artifact(self.saved)}, {55: self.bundle(self.saved)})
        self.assertTrue(self.listed)
        self.assertEqual((out / f"signatures-{self.saved}.txt").read_text(), "theorem t 1\n")
        self.assertFalse((self.dir / ".lake/build/old").exists())


class MainStatements(unittest.TestCase):
    """main_statements.py: Main state fails when an existing statement changed; acceptances are
    bound to what was reviewed (second review, items 1, 2 and 5)."""

    P, T = "1" * 40, "2" * 40

    def run_on(self, old, new, *flags, previous=P, target=T):
        with tempfile.TemporaryDirectory() as tmp:
            (Path(tmp) / "new").write_text(new)
            if old is not None:
                (Path(tmp) / "old").write_text(old)
            ids = ["--target", target] + (["--previous-sha", previous] if previous else [])
            with mock.patch.dict(os.environ, {"GITHUB_STEP_SUMMARY": ""}), \
                    contextlib.redirect_stdout(io.StringIO()) as printed:
                status = main_statements.main([*ids, *flags, str(Path(tmp) / "old"), str(Path(tmp) / "new")])
        return status, printed.getvalue()

    def accept(self, names, baseline=P, target=T):
        return ["--accept-baseline", baseline, "--accept-target", target, "--accept-names", names]

    OLD = "theorem a 1\ndef b 2 3\ntheorem _private.X.0.c 4\n"
    CHANGED = "theorem a 9\ndef b 2 4\ntheorem _private.X.0.c 4\n"

    def test_additions_and_proofs_are_fine(self):
        self.assertEqual(self.run_on(self.OLD, self.OLD + "theorem d 5\ndef e 6 7\n")[0], 0)

    def test_a_changed_or_removed_statement_fails(self):
        status, printed = self.run_on(self.OLD, "theorem a 9\n" + self.OLD.split("\n", 1)[1])
        self.assertEqual(status, 1)
        self.assertIn("- `a` changed", printed)
        status, printed = self.run_on(self.OLD, "theorem a 1\ntheorem _private.X.0.c 4\n")
        self.assertEqual(status, 1)
        self.assertIn("- `b` removed", printed)
        self.assertIn(f"-f accept_baseline={self.P} -f accept_target={self.T} -f accept_names=b", printed)

    def test_private_definitions_are_exempt_as_in_the_check(self):
        self.assertEqual(self.run_on(self.OLD, "theorem a 1\ndef b 2 3\n")[0], 0)

    def test_nothing_to_compare_with_fails_unless_built_from_scratch(self):
        for old, previous in ((None, None), (None, self.P), ("", self.P), ("\n", self.P)):
            self.assertEqual(self.run_on(old, self.OLD, previous=previous)[0], 1)
            status, printed = self.run_on(old, self.OLD, "--from-scratch", previous=previous)
            self.assertEqual(status, 0)
            self.assertIn("start a new baseline", printed)

    def test_a_malformed_dump_is_never_compared(self):
        for old in ("theorem a 1\ngarbage\n", "theorem a 1\ntheorem b\n", "garbage\n"):
            status, printed = self.run_on(old, self.OLD)
            self.assertEqual(status, 1, old)
            self.assertIn("malformed", printed)
        # a new dump that is malformed or empty fails even from scratch: it would be the next baseline
        for new in ("theorem a 1\ngarbage\n", ""):
            self.assertEqual(self.run_on(self.OLD, new, "--from-scratch")[0], 1)
            self.assertEqual(self.run_on(None, new, "--from-scratch", previous=None)[0], 1)

    def test_only_the_reviewed_names_at_the_reviewed_commits_are_accepted(self):
        status, printed = self.run_on(self.OLD, self.CHANGED, *self.accept("a, b"))
        self.assertEqual(status, 0)
        self.assertIn("- `a` changed (accepted)", printed)
        # a change not on the list still fails, and is shown
        status, printed = self.run_on(self.OLD, self.CHANGED, *self.accept("a"))
        self.assertEqual(status, 1)
        self.assertIn("Not accepted: b", printed)
        # another baseline or another target: nothing is accepted
        for baseline, target in ((self.T, self.T), (self.P, self.P), ("", self.T)):
            status, printed = self.run_on(self.OLD, self.CHANGED, *self.accept("a b", baseline, target))
            self.assertEqual(status, 1, (baseline, target))
            self.assertIn("does not apply", printed)
        # names listed that did not change are reported, not a reason to fail
        status, printed = self.run_on(self.OLD, self.CHANGED, *self.accept("a b z"))
        self.assertEqual(status, 0)
        self.assertIn("Listed but not changed: z", printed)

    def test_a_from_scratch_failure_asks_for_a_from_scratch_acceptance(self):
        printed = self.run_on(self.OLD, self.CHANGED, "--from-scratch")[1]
        self.assertIn("main_state.yml --ref main -f full=true -f accept_baseline=", printed)


class Workflow(unittest.TestCase):
    """What pr_check.yml does with a verdict against the saved build (review item 1); the steps
    themselves only run on GitHub."""

    text = (Path(__file__).resolve().parent.parent.parent / ".github/workflows/pr_check.yml").read_text()

    def test_only_merge_or_read_against_the_saved_build_is_published(self):
        self.assertIn("if: env.BASE_SHA != env.MAIN_SHA && steps.check.outputs.verdict != 'merge' "
                      "&& steps.check.outputs.verdict != 'read'", self.text)
        self.assertIn("name: verdict-${{ steps.tip.outputs.verdict || steps.check.outputs.verdict }}", self.text)
        tip = self.text[self.text.index("id: tip"):self.text.index("name: Publish the verdict")]
        self.assertIn('--base "$MAIN_SHA" --head "$HEAD_SHA"', tip)
        self.assertIn("rm -rf work/.lake/build", tip)

    def test_a_run_that_publishes_no_verdict_leaves_an_error_to_retry(self):
        # second review, item 9: a job out of time publishes nothing itself
        job = self.text[self.text.index("  unfinished:"):]
        self.assertIn("needs: verdict", job)
        self.assertIn("if: always() && needs.verdict.result != 'success'", job)
        self.assertIn("name: verdict-error", job)
        self.assertIn('.created_at >= \\"$started\\"', job)       # only this attempt's verdicts count


class MainStateWorkflow(unittest.TestCase):
    text = (Path(__file__).resolve().parent.parent.parent / ".github/workflows/main_state.yml").read_text()

    def test_signatures_are_kept_apart_for_two_weeks(self):
        upload = self.text[self.text.index("name: main-signatures"):]
        self.assertIn("retention-days: 14", upload)
        self.assertLess(self.text.index("main_statements.py"), self.text.index("uses: actions/upload-artifact"))

    def test_the_run_name_tells_a_build_from_scratch(self):
        self.assertIn(f"&& '{auto_merge.FROM_SCRATCH}' ||", self.text)


class Report(unittest.TestCase):
    def test_summary_names_the_saved_base_and_main(self):
        with tempfile.TemporaryDirectory() as out:
            args = types.SimpleNamespace(out=out, pr=1, head="a" * 40, base="b" * 40, main="c" * 40, behind="23")
            verdict.report(args, "merge", [], "")
            data = json.loads((Path(out) / "verdict.json").read_text())
            self.assertEqual((data["schema"], data["base_sha"], data["main_sha"]), (1, "b" * 40, "c" * 40))
            summary = (Path(out) / "summary.md").read_text()
            self.assertIn("`bbbbbbbbbbbb`", summary)
            self.assertIn("`cccccccccccc`, 23 commits further", summary)


if __name__ == "__main__":
    unittest.main()
