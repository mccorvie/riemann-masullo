#!/usr/bin/env bash
# Merger's tool (the integrator's when no merger session is running): check every open pull
# request from outside the project, several at a time, and merge the ones that need no judgment.
#
#   scripts/triage_prs.sh            check and report
#   scripts/triage_prs.sh --apply    also merge the clean ones, and tell authors what failed
#
# Each pull request is checked once per head commit with scripts/check_pr.sh (under bwrap), and
# the result is kept in .agent/pr-checks/. Verdicts:
#   merge   it passes, adds no `sorry`, and its added lines are ordinary proof text
#   read    it passes, but something deserves a look first: a split (a new `sorry`), a new
#           definition or file, an attribute, a `#` command, an import, or anything that could
#           run code when the file is built. Read the diff, then merge it by hand.
#           Also a docstring that cites the paper, or a new declaration outside ForMathlib/
#           that is not `private`: a new definition from the paper, or a new theorem from the
#           paper left as `sorry`, is a statement, so label it `integrator`; a new theorem
#           proved in the pull request is not, so merge it.
#   fail    it does not merge into main, build, pass the lint, or keep existing statements
# Draft pull requests, and those labelled `integrator`, are left alone.
set -uo pipefail
script_dir=$(cd "$(dirname "$0")" && pwd)
main=$(dirname "$(git rev-parse --path-format=absolute --git-common-dir)")
cd "$main"
apply=0; [ "${1:-}" = --apply ] && apply=1
mkdir -p .agent/pr-checks
# One triage at a time: two would check the same pull request in the same scratch worktree.
exec 9>.agent/pr-checks/.lock
flock -n 9 || { echo "another triage is running; try again when it has finished"; exit 0; }
list=$(gh api --paginate "repos/{owner}/{repo}/pulls?state=open&per_page=100" --jq \
  '.[] | select(.base.ref == "main" and (.draft | not)) | select(.author_association | IN("OWNER","MEMBER","COLLABORATOR") | not)
       | select(any(.labels[]; .name == "integrator") | not)
       | "\(.number) \(.head.sha) \(.user.login)"') || exit 1
[ -n "$list" ] || { echo "no open pull requests from outside the project"; exit 0; }

# Fetch main and every head once, so the parallel checks do not fight over git's ref locks.
refs=(main); while read -r n sha who; do refs+=("+pull/$n/head:refs/remotes/origin/pr-$n"); done <<<"$list"
git fetch -q origin "${refs[@]}" || exit 1
base=$(git rev-parse --verify 'origin/main^{commit}') || exit 1
export CHECK_PR_BASE="$base"

check_one() {
  local n=$1 sha=$2 who=$3 out=".agent/pr-checks/$1-$2.txt"
  CHECK_PR_NO_FETCH=1 CHECK_PR_HEAD="$sha" scripts/check_pr.sh "$n" >"$out.tmp" 2>&1
  echo "exit=$?" >>"$out.tmp" && mv "$out.tmp" "$out" || return 1
  printf '%s %s %s\n' "$n" "$sha" "$who"
}
export -f check_one

ready_prs() {
  local n sha who out
  local -a pending=()
  while read -r n sha who; do
    out=".agent/pr-checks/$n-$sha.txt"
    # Older reports did not record which head was actually built.
    if [ -s "$out" ] && grep -qF "checking $sha against " "$out"; then
      printf '%s %s %s\n' "$n" "$sha" "$who"
    else
      pending+=("$n $sha $who")
    fi
  done <<<"$list"
  if [ "${#pending[@]}" -gt 0 ]; then
    printf '%s\n' "${pending[@]}" | xargs -P 6 -L 1 bash -c 'check_one "$@"' _
  fi
}

# Consume cached results immediately, then each new report as its worker finishes.
# One reader owns the GitHub actions and merge count.
exec {results}< <(ready_prs)
workers=$!
merged=0
while read -r -u "$results" n sha who; do
  out=".agent/pr-checks/$n-$sha.txt"
  current=$(gh pr view "$n" --json title,state,baseRefName,isDraft,labels,headRefOid --jq '
    select(.state == "OPEN" and .baseRefName == "main" and (.isDraft | not))
    | select(any(.labels[]; .name == "integrator") | not)
    | .headRefOid + " " + .title') || { echo "error  #$n  could not refresh the PR"; continue; }
  [[ "$current" == "$sha "* ]] || { echo "skip   #$n  head or review status changed"; continue; }
  title=${current#* }
  if grep -q '^exit=0' "$out" && grep -q 'lint and build: pass' "$out" &&
     grep -q 'statements: none of' "$out" && grep -q 'definitions: none contains sorry' "$out"; then
    why=$(bash "$script_dir/proof_review.sh" "$base" "$sha") || {
      echo "error  #$n  cannot read the diff; it will be retried"; continue
    }
    if [ -z "$why" ]; then
      echo "merge  #$n  $who  $title"
      if [ $apply = 1 ]; then gh pr merge "$n" --squash --match-head-commit "$sha" >/dev/null 2>&1 && merged=$((merged+1)) || echo "       could not merge (head or base changed?)"; fi
    else
      echo "read   #$n  $who  ($why)  $title"
    fi
  elif ! grep -qE 'REFUSED|lint or build: FAIL|statement or definition changed|^removed:|definitions containing sorry' "$out"; then
    # The check itself broke (a git or tooling hiccup), which says nothing about the pull
    # request. Forget the result so that the next run tries again.
    echo "error  #$n  $who  the check did not complete; it will be retried"
    rm -f "$out"
  else
    echo "fail   #$n  $who  $title"
    grep -vE '^(hint|  - |exit=)' "$out" | tail -n 4 | sed 's/^/         /'
    if [ $apply = 1 ] && [ ! -e "$out.told" ]; then
      gh pr comment "$n" --body "Automated check against the current \`main\` (\`scripts/check_pr.sh\`) did not pass for commit \`${sha:0:7}\`:

\`\`\`
$(grep -vE '^(hint|  - |exit=)' "$out" | tail -n 15)
\`\`\`

If \`main\` has moved, merging it into your branch and rebuilding usually sorts it out. This comment was generated automatically." >/dev/null 2>&1 && touch "$out.told"
    fi
  fi
done
wait "$workers" || exit 1
[ $merged = 0 ] || echo "merged $merged; now run: git pull && lake build && scripts/issues.py --apply"
