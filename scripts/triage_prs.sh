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
#           that is not `private`: if it states something from the paper it is a statement,
#           so label it `integrator` instead of merging it.
#   fail    it does not merge into main, build, pass the lint, or keep existing statements
# Draft pull requests, and those labelled `integrator`, are left alone.
set -uo pipefail
main=$(dirname "$(git rev-parse --path-format=absolute --git-common-dir)")
cd "$main"
apply=0; [ "${1:-}" = --apply ] && apply=1
mkdir -p .agent/pr-checks
# One triage at a time: two would check the same pull request in the same scratch worktree.
exec 9>.agent/pr-checks/.lock
flock -n 9 || { echo "another triage is running; try again when it has finished"; exit 0; }
list=$(gh api --paginate "repos/{owner}/{repo}/pulls?state=open&per_page=100" --jq \
  '.[] | select(.draft | not) | select(.author_association | IN("OWNER","MEMBER","COLLABORATOR") | not)
       | select(any(.labels[]; .name == "integrator") | not)
       | "\(.number) \(.head.sha) \(.user.login)"')
[ -n "$list" ] || { echo "no open pull requests from outside the project"; exit 0; }

# Fetch main and every head once, so the parallel checks do not fight over git's ref locks.
refs=(main); while read -r n sha who; do refs+=("pull/$n/head:refs/remotes/origin/pr-$n"); done <<<"$list"
git fetch -q origin "${refs[@]}"

check_one() {
  local n=$1 sha=$2 out=".agent/pr-checks/$1-$2.txt"
  [ -s "$out" ] && return
  CHECK_PR_NO_FETCH=1 scripts/check_pr.sh "$n" >"$out.tmp" 2>&1
  echo "exit=$?" >>"$out.tmp"; mv "$out.tmp" "$out"
}
export -f check_one
awk '{print $1, $2}' <<<"$list" | xargs -P 6 -L 1 bash -c 'check_one "$0" "$1"'

# Added lines that make a pull request worth reading before it is merged.
# Importing Mathlib or this library, and silencing a linter, are routine and are not flagged.
eyes='^\+[[:space:]]*(#|@\[|open Lean|attribute|macro|syntax|notation|elab|initialize|unsafe|instance|def |abbrev |structure|class |inductive|axiom|opaque|noncomputable)|run_|by_elab|simproc|Lean\.|Elab|Meta\.|IO\.|extern|implemented_by|native'
routine='^\+[[:space:]]*((public )?import (Mathlib|RiemannMasullo)\.[A-Za-z0-9_.]+[[:space:]]*$|set_option linter\.[A-Za-z0-9_.]+ (true|false) in[[:space:]]*$)'
# A proof may add helper lemmas, but a new declaration taken from the paper is a statement, and
# statements are the integrator's. Two signs of one are flagged for reading: a docstring that
# cites the paper, and a declaration outside ForMathlib/ that is not `private`.
decl='[[:space:]]*(@\[[^]]*\][[:space:]]*)*((public|protected|noncomputable|nonrec|scoped|local)[[:space:]]+)*(theorem|lemma|def|abbrev|instance|structure|class|inductive)[[:space:]]+'
declared() {  # names declared on those diff lines of stdin that start with the sign $1
  grep -E "^[$1]$decl" | sed -E "s/^[$1]$decl//; s/[[:space:]:({[].*//" | sort -u
}
merged=0
while read -r n sha who; do
  out=".agent/pr-checks/$n-$sha.txt"
  title=$(gh pr view "$n" --json title --jq .title 2>/dev/null)
  added=$(git diff "origin/main...origin/pr-$n" | grep -E '^\+[^+]' || true)
  newfiles=$(git diff --diff-filter=A --name-only "origin/main...origin/pr-$n")
  if grep -q '^exit=0' "$out" && grep -q 'lint and build: pass' "$out" &&
     grep -q 'statements: none of' "$out" && grep -q 'definitions: none contains sorry' "$out"; then
    why=""
    grep -qw sorry <<<"$added" && why="adds a sorry"
    [ -z "$newfiles" ] || why="${why:+$why, }new file"
    rest=$(grep -vE "$routine" <<<"$added" || true)
    grep -qE "$eyes|^\+[[:space:]]*(import|set_option) " <<<"$rest" && why="${why:+$why, }not plain proof text"
    grep -qE '^\+.*Paper:' <<<"$added" && why="${why:+$why, }cites the paper"
    # A name that is also on a removed line is an existing declaration whose first line was
    # rewritten to hold the proof, not a new one.
    lib=$(git diff "origin/main...origin/pr-$n" -- RiemannMasullo ':(exclude)RiemannMasullo/ForMathlib')
    newdecl=$(comm -23 <(declared + <<<"$lib") <(declared - <<<"$lib") | paste -sd' ')
    [ -z "$newdecl" ] || why="${why:+$why, }new public declaration: $newdecl"
    if [ -z "$why" ]; then
      echo "merge  #$n  $who  $title"
      if [ $apply = 1 ]; then gh pr merge "$n" --squash >/dev/null 2>&1 && merged=$((merged+1)) || echo "       could not merge (conflict with a merge made meanwhile?)"; fi
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
done <<<"$list"
[ $merged = 0 ] || echo "merged $merged; now run: git pull && lake build && scripts/issues.py --apply"
