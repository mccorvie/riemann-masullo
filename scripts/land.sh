#!/usr/bin/env bash
# Merge finished proofs from the project's launcher, and list everything that needs review.
#
#   scripts/land.sh                      show the decisions
#   scripts/land.sh --apply              merge, then update and rebuild main
#   scripts/land.sh --apply --no-pull    merge on GitHub only (used by scripts/pool.sh)
set -euo pipefail
script_dir=$(cd "$(dirname "$0")" && pwd)
cd "$(dirname "$(git rev-parse --path-format=absolute --git-common-dir)")"
apply=0; pull=1
for arg in "$@"; do
  case $arg in --apply) apply=1 ;; --no-pull) pull=0 ;; esac
done
list=$(gh api --paginate "repos/{owner}/{repo}/pulls?state=open&per_page=100" --jq '
  sort_by(.number) | .[] | [
    .number, .head.ref, .author_association, (.head.repo.id == .base.repo.id),
    .base.ref, .base.sha, .head.sha, .draft, any(.labels[]; .name == "integrator"),
    ((.body // "") | contains("Statement check: none of")), .title
  ] | @tsv')
merged=0
while IFS=$'\t' read -r pr branch assoc same_repo target base sha draft integrator handin title; do
  [ -n "$pr" ] || continue
  reason=""
  if [ "$draft" = true ]; then reason="draft"
  elif [ "$integrator" = true ]; then reason="labelled integrator"
  elif [ "$target" != main ]; then reason="targets $target"
  elif [[ ! "$branch" =~ ^prover/[0-9]+$ ]]; then reason="not a prover branch"
  elif [[ "$same_repo" != true || ! "$assoc" =~ ^(OWNER|MEMBER|COLLABORATOR)$ ]]; then reason="from outside the project"
  elif [ "$handin" != true ]; then reason="no statement check recorded"
  elif ! git fetch -q origin "$base" "$sha"; then reason="could not fetch the PR commits"
  else
    files=$(git diff --no-renames --name-only "$base...$sha")
    if grep -qvE '^RiemannMasullo/.*\.lean$' <<<"$files" || grep -q '^RiemannMasullo/External/' <<<"$files"; then
      reason="touches files outside the library"
    else
      reason=$(bash "$script_dir/proof_review.sh" "$base" "$sha")
    fi
  fi
  if [ -n "$reason" ]; then
    echo "review  #$pr  $branch  ($reason)  $title"
  else
    echo "merge   #$pr  $branch  $title"
    if [ "$apply" = 1 ]; then
      if gh pr merge "$pr" --squash --delete-branch --match-head-commit "$sha" >/dev/null; then
        merged=$((merged+1))
      fi
    fi
  fi
done <<<"$list"
if [ "$apply" = 1 ] && [ "$pull" = 1 ] && [ "$merged" -gt 0 ]; then
  git pull -q origin main
  lake build 2>&1 | tail -n 1
fi
