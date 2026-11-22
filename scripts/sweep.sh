#!/usr/bin/env bash
# Close out one library file with a single agent (a "sweeper"): it takes every open, unclaimed
# proof issue of that file at once, works through them in one worktree, and hands in one pull
# request that closes the ones it proved. Single provers leave a file's hard tail behind; a
# sweeper has the whole file, more time and a stronger model.
#
#   scripts/sweep.sh RiemannMasullo/<Chapter>/<File>.lean [--model M] [--effort E] [--note-file F] [--dry-run]
#
# What it does:
#   1. lists the file's open proof issues (by the `<!-- sorry: path::name -->` marker);
#   2. opens a `sweep` issue with that list and what project members wrote on those issues,
#      and marks the unclaimed ones `claimed`, so that nobody else works in the file meanwhile;
#   3. runs `scripts/agent.sh sweeper <that issue>` (prompt: prompts/sweeper.md), which builds,
#      checks that no statement changed, and opens the pull request;
#   4. releases the issues the pull request does not close.
# Issues that someone else has claimed are left alone and named to the agent as such.
#
#   scripts/sweep.sh --resume <sweep issue> [--model M] [--effort E]
# picks up a sweeper that was interrupted (its worktree, with whatever it had proved, is still
# there): the agent continues in place, then the hand-in and the release run as usual.
set -euo pipefail
resume=""
if [ "${1:-}" = --resume ]; then resume=${2:?the sweep issue number}; shift 2; set -- "resume" "$@"; fi
file=${1:?usage: sweep.sh RiemannMasullo/<Chapter>/<File>.lean [--model M] [--effort E] [--dry-run]}
shift
model=gpt-6.2-astra; effort=xhigh; dry=0; note=""
while [ $# -gt 0 ]; do
  case $1 in
    --model) model=$2; shift 2 ;;
    --effort) effort=$2; shift 2 ;;
    --dry-run) dry=1; shift ;;
    --note-file) note=$2; shift 2 ;;      # text added to the sweep issue: priorities, hints
    *) echo "unknown option $1" >&2; exit 2 ;;
  esac
done
main=$(dirname "$(git rev-parse --path-format=absolute --git-common-dir)")
cd "$main"
work=$(mktemp -d); trap 'rm -rf "$work"' EXIT

release() {   # release what the sweeper's pull request does not close; $1 = sweep issue
  local n=$1 closes kept=0 released=0 i
  closes=$(gh pr list --head "sweeper/$n" --state all --json body --jq '.[0].body // ""' |
    grep -oiE '(close[sd]?|fix(e[sd])?|resolve[sd]?)[: ]+#[0-9]+' | grep -oE '[0-9]+$' | sort -u || true)
  while read -r i; do
    if grep -qx "$i" <<<"$closes"; then kept=$((kept + 1)); continue; fi
    gh issue edit "$i" --remove-label claimed >/dev/null 2>&1 || true
    gh issue comment "$i" --body "The sweeper did not prove this one in its pass; what it tried and what blocked it is on #$n. Free to take." >/dev/null
    released=$((released + 1))
  done <"$work/mine.txt"
  echo "sweep #$n: $kept proved in the pull request, $released released"
}

if [ -n "$resume" ]; then
  n=$resume; wt="$(dirname "$main")/$(basename "$main")-wt/sweeper-$n"
  [ -d "$wt" ] || { echo "no worktree at $wt to resume" >&2; exit 1; }
  gh api "repos/{owner}/{repo}/issues/$n" --jq .body | grep -oE '^\| #[0-9]+' | grep -oE '[0-9]+' >"$work/mine.txt"
  [ -s "$work/mine.txt" ] || { echo "#$n does not look like a sweep issue" >&2; exit 1; }
  echo "resuming the sweeper of #$n in $wt"
  codex exec --sandbox workspace-write -C "$wt" -o "$wt/.agent/last-message.md" -m "$model" \
    -c "model_reasoning_effort=\"$effort\"" "You are the sweeper described in .agent/PROMPT.md in this directory, and you were interrupted part-way (the machine ran out of memory; nothing you did caused it). Your work so far is in the working tree and your notes are in .agent/NOTES.md. Read .agent/PROMPT.md again, look at what is already proved and whether the file still builds, repair anything left half-edited, and then carry on from where you stopped. You have about two more hours. Finish as the prompt says, with .agent/PR.md and, if anything is left, .agent/REPORT.md." \
    >>"$wt/.agent/log.txt" 2>&1 </dev/null || true
  scripts/agent.sh sweeper "$n" --handin --cli codex --model "$model" --effort "$effort" </dev/null || true
  release "$n"
  exit 0
fi
[ -f "$file" ] || { echo "no such file: $file" >&2; exit 2; }

# The plan: which issues, and the text of the sweep issue. Only text written by the owner,
# members or collaborators is quoted, as everywhere else that feeds an agent's prompt.
python3 - "$file" "$work" <<'EOF'
import json, re, subprocess, sys
path, work = sys.argv[1], sys.argv[2]
MEMBER = ("OWNER", "MEMBER", "COLLABORATOR")


def api(url, jq):
    out = subprocess.run(["gh", "api", "--paginate", url, "--jq", jq], capture_output=True, text=True)
    if out.returncode:
        sys.exit(out.stderr)
    return [json.loads(line) for line in out.stdout.splitlines() if line.strip()]


issues = api("repos/{owner}/{repo}/issues?state=open&labels=proof&per_page=100",
             ".[] | select(.pull_request | not) | {number, body, labels: [.labels[].name]} | tojson")
lines = open(path).read().splitlines()
mine, others = [], []
for issue in sorted(issues, key=lambda i: i["number"]):
    m = re.search(r"<!-- sorry: (\S+?)::(\S+) -->", issue["body"] or "")
    if not m or m.group(1) != path:
        continue
    name = m.group(2)
    at = next((k + 1 for k, text in enumerate(lines)
               if re.match(rf"\s*(?:\w+\s+)*(?:theorem|lemma|def|instance|abbrev)\s+{re.escape(name)}\b", text)), None)
    if at is None:
        continue                                  # already proved or renamed on this checkout
    row = dict(number=issue["number"], name=name, line=at)
    (others if {"claimed", "stuck", "blocked", "gap"} & set(issue["labels"]) else mine).append(row)
if not mine:
    sys.exit(f"{path}: no open, unclaimed proof issue")

body = [f"Close out `{path}`: prove every remaining `sorry` listed here, in one pull request. "
        "The rules are in `prompts/sweeper.md`.", "",
        "| Issue | Declaration | Line |", "|---|---|---|"]
body += [f"| #{r['number']} | `{r['name']}` | {r['line']} |" for r in mine]
if others:
    body += ["", "Claimed by someone else, or set aside: leave these declarations alone.", ""]
    body += [f"- #{r['number']} `{r['name']}`" for r in others]
notes = []
for r in mine:
    comments = api(f"repos/{{owner}}/{{repo}}/issues/{r['number']}/comments?per_page=100",
                   ".[] | {body, association: .author_association} | tojson")
    kept = [c["body"].strip() for c in comments if c["association"] in MEMBER and len(c["body"]) > 300
            and not re.match(r"\s*(claim|releas)", c["body"], re.I)]
    if kept:
        notes += [f"### #{r['number']} `{r['name']}`", ""] + [text[:4000] for text in kept[-2:]] + [""]
if notes:
    body += ["", "## What earlier attempts reported", ""] + notes
open(f"{work}/body.md", "w").write("\n".join(body) + "\n")
open(f"{work}/mine.txt", "w").write("".join(f"{r['number']}\n" for r in mine))
print(f"{path}: {len(mine)} to prove" + (f", {len(others)} left to others" if others else ""))
EOF

if [ -n "$note" ]; then { echo; echo "## From the integrator"; echo; cat "$note"; } >>"$work/body.md"; fi
if [ $dry = 1 ]; then cat "$work/body.md"; exit 0; fi

chapter=$(sed -nE 's#^RiemannMasullo/(Ch[0-9]+|App[A-E])_.*#\1#p' <<<"$file" | tr '[:upper:]' '[:lower:]' | sed 's/^app\(.\)/app\U\1/')
args=(--title "Sweep: close out \`${file#RiemannMasullo/}\`" --body-file "$work/body.md" --label sweep)
[ -z "$chapter" ] || args+=(--label "$chapter")
n=$(gh issue create "${args[@]}" | sed -n 's#.*/issues/\([0-9]*\)$#\1#p')
[ -n "$n" ] || { echo "could not open the sweep issue" >&2; exit 1; }
echo "sweep issue #$n"
while read -r i; do
  gh issue edit "$i" --add-label claimed >/dev/null 2>&1 || true
  gh issue comment "$i" --body "Claimed by a sweeper agent that is closing out the whole file in one pull request (#$n)." >/dev/null
done <"$work/mine.txt"

scripts/agent.sh sweeper "$n" --model "$model" --effort "$effort" </dev/null || true

release "$n"
