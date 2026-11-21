#!/usr/bin/env bash
# Bring the proof issues in line with main: open one for each `sorry` that has none, close the
# ones whose `sorry` is gone. A wrapper round scripts/issues.py that anyone with write access
# can run at any time, from anywhere in the repository:
#
#   scripts/sync_issues.sh            do it
#   scripts/sync_issues.sh --dry-run  only list what would change
#
# issues.py must run in a checkout that nothing else touches while it builds and reads the
# files (it stops if the checkout moves under it). The main checkout is not such a place: the
# integrator pulls there all the time. So this keeps a worktree of its own, "sync", brings it
# to the tip of main, builds it there, and runs issues.py in it. One run at a time.
set -euo pipefail
main=$(dirname "$(git rev-parse --path-format=absolute --git-common-dir)")
wt="$(dirname "$main")/$(basename "$main")-wt/sync"
mkdir -p "$main/.agent"
exec 7>"$main/.agent/sync.lock"
flock -n 7 || { echo "another sync is running; try again when it has finished"; exit 0; }
git -C "$main" fetch -q origin main
if [ ! -d "$wt" ]; then
  git -C "$main" worktree add -q --detach "$wt" origin/main
  mkdir -p "$wt/.lake" && ln -sfn "$main/.lake/packages" "$wt/.lake/packages"
  [ ! -d "$main/.lake/build" ] || cp -a --reflink=auto "$main/.lake/build" "$wt/.lake/build"
fi
cd "$wt"
git checkout -q --detach origin/main
echo "syncing at $(git rev-parse --short HEAD); building (this is the slow part)"
lake build RiemannMasullo >/dev/null 2>&1 || { echo "main does not build; fix that first" >&2; lake build RiemannMasullo 2>&1 | tail -n 20 >&2; exit 1; }
if [ "${1:-}" = --dry-run ]; then scripts/issues.py; else scripts/issues.py --apply "$@"; fi
