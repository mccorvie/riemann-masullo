#!/usr/bin/env bash
# Run one agent on one issue in its own worktree, and hand in its work.
#
#   scripts/agent.sh <prover|digester|scout> <issue number|next> [options]
#
# With no mode option it does three steps: set up, run the agent, hand in. To drive the agent
# yourself (for example an interactive Codex or Claude session), do the outer two separately:
#
#   --setup    create the worktree, claim the issue, write the prompt to .agent/PROMPT.md, and
#              stop. Start any agent in that directory and tell it:
#                  Read .agent/PROMPT.md and follow it.
#   --handin   build, commit, push and open the pull request from that worktree, and post
#              .agent/REPORT.md as a comment on the issue.
#
# Other options:
#   --cli codex|claude   which agent to run (default: codex; claude for scouts)
#   --model NAME         model to pass to the CLI
#   --effort LEVEL       reasoning effort for Codex (low, medium, high, xhigh)
#   --dry-run            print the prompt and change nothing
#   --force              take an issue that is labelled `claimed` or `blocked`, or discard an
#                        existing worktree
#
# The agent needs no git access, and only scouts need the network: this script does the building,
# committing, pushing and commenting. Relaunching on an issue that has an open pull request
# resumes that branch and shows the agent the review comments.
#
# The repository is public, so issue text is not all trustworthy, and an agent's output is not
# either. Three guards:
#   - only text written by the owner, members or collaborators reaches an agent's prompt;
#   - a prover or digester may change only Lean files under RiemannMasullo/ (not External/);
#   - the hand-in build runs under bwrap with no network and no home directory, because building
#     Lean can execute code;
#   - the hand-in compares the signature of every declaration with what it was when the agent
#     started (scripts/signatures.sh), and refuses work that changed an existing statement.
#
# It works from a fork too: issues and pull requests are those of the `upstream` remote if there
# is one (otherwise `origin`), and your branch is pushed to `origin`.
# Needs: gh (logged in), jq, bwrap, and the Codex or Claude Code CLI.
set -euo pipefail

# Everything runs inside main, so bash has read the whole file before it starts. A launcher
# waits on its agent for a long time, and the file may be edited or updated meanwhile.
main() {

usage="usage: agent.sh <prover|digester|scout> <issue|next> [--setup|--handin] [--cli codex|claude] [--model M] [--effort E] [--dry-run] [--force]"
role=${1:?$usage}
target=${2:?$usage}
shift 2
cli=""; model=""; effort=""; mode=all; dry=0; force=0
while [ $# -gt 0 ]; do
  case $1 in
    --setup) mode=setup; shift ;;
    --handin) mode=handin; shift ;;
    --cli) cli=$2; shift 2 ;;
    --model) model=$2; shift 2 ;;
    --effort) effort=$2; shift 2 ;;
    --dry-run) dry=1; shift ;;
    --force) force=1; shift ;;
    *) echo "unknown option $1" >&2; echo "$usage" >&2; exit 2 ;;
  esac
done
case $role in
  prover) label=proof ;;
  digester) label=section ;;
  scout) label="" ;;
  *) echo "unknown role $role" >&2; exit 2 ;;
esac
if [ $mode = all ] && [ -z "$cli" ]; then [ "$role" = scout ] && cli=claude || cli=codex; fi
who="${cli:-interactive session}${model:+, $model}${effort:+, $effort effort}"

main=$(dirname "$(git rev-parse --path-format=absolute --git-common-dir)")
cd "$main"
up=origin; git remote get-url upstream >/dev/null 2>&1 && up=upstream
slug() { git remote get-url "$1" | sed -E 's#^(git@github\.com:|https://github\.com/|ssh://git@github\.com/)##; s#\.git$##'; }
export GH_REPO=$(slug "$up")           # every gh command below addresses the upstream repository
api="repos/$GH_REPO"
member='IN("OWNER","MEMBER","COLLABORATOR")'   # whose text may reach an agent's prompt

if [ "$target" = next ]; then
  [ -n "$label" ] || { echo "'next' needs the prover or digester role" >&2; exit 2; }
  # Proofs are handed out bottom-up through the import graph, a few per file at a time; section
  # issues oldest first. See scripts/next_issue.py.
  target=$(python3 "$main/scripts/next_issue.py" "$label") || target=""
  [ -n "$target" ] || { echo "no unclaimed $label issue" >&2; exit 1; }
fi
n=$target
branch="$role/$n"
wt="$(dirname "$main")/$(basename "$main")-wt/$role-$n"
head=$branch; [ "$(slug origin)" = "$GH_REPO" ] || head="$(slug origin | cut -d/ -f1):$branch"
pr_number() { gh pr list --head "$branch" --author @me --state open --json number --jq '.[0].number // empty'; }
note() { gh issue comment "$n" --body "$1" >/dev/null; }
label() { gh issue edit "$n" "$@" >/dev/null 2>&1 || true; }   # needs triage rights; the Claims workflow covers everyone else
released() {   # "Released. " when no pull request holds the claim; the Claims workflow reads that word
  # The issue is also labelled `stuck`, so that `next` does not hand it straight to another agent
  # before the integrator has looked at why this one stopped.
  [ "$role" = scout ] || [ -n "$(pr_number)" ] || { label --remove-label claimed --add-label stuck; printf 'Released. '; }
}
fail() {   # refuse the hand-in: tell the issue why, release the claim, keep the worktree
  note "$(released)$1"
  echo "hand-in refused (see issue #$n); worktree kept at $wt" >&2; exit 1
}
sandboxed() {   # run a command in the worktree: no network, no home directory, nothing else writable
  command -v bwrap >/dev/null || { echo "bwrap (bubblewrap) is required for the hand-in build" >&2; exit 2; }
  bwrap --ro-bind / / --dev /dev --proc /proc --tmpfs /tmp --tmpfs /run --tmpfs "$HOME" \
    --ro-bind "$HOME/.elan" "$HOME/.elan" --ro-bind "$main/.lake/packages" "$main/.lake/packages" \
    --bind "$wt" "$wt" --chdir "$wt" --unshare-net --die-with-parent "$@"
}

# ---- set up ----
if [ $mode != handin ]; then
  issue=$(gh api "$api/issues/$n")
  if [ "$(jq -r ".author_association | $member" <<<"$issue")" != true ] && [ $force = 0 ]; then
    echo "issue #$n was opened by someone outside the project, and its text would become the agent's" >&2
    echo "instructions. Read it first; then re-file it yourself, or pass --force." >&2; exit 1
  fi
  labels=$(jq -r '[.labels[].name] | join(" ")' <<<"$issue")
  if [[ " $labels " == *" blocked "* ]] && [ $force = 0 ]; then
    echo "issue #$n is blocked: what it needs first is not on main yet (use --force to try anyway)" >&2; exit 1
  fi
  git fetch -q "$up"; [ "$up" = origin ] || git fetch -q origin
  base="$up/main"; pr=""
  [ "$role" = scout ] || pr=$(pr_number)
  [ -z "$pr" ] || base="origin/$branch"
  if [ "$role" != scout ] && [ -z "$pr" ] && [ $force = 0 ] && [[ " $labels " == *" claimed "* ]]; then
    echo "issue #$n is already claimed (use --force to take it anyway)" >&2; exit 1
  fi
  comments=$(gh api --paginate "$api/issues/$n/comments" --jq \
    ".[] | select(.author_association | $member) | \"\n### Comment by \(.user.login)\n\n\(.body)\n\"")
  skipped=$(gh api --paginate "$api/issues/$n/comments" --jq \
    "[.[] | select(.author_association | $member | not)] | length" | awk '{s+=$1} END {print s+0}')
  [ "$skipped" = 0 ] || echo "note: left out $skipped comment(s) by people outside the project" >&2

  prompt="$(cat "prompts/$role.md")

---

## Your issue: #$n

$(jq -r '"**\(.title)**\n\n\(.body // "")"' <<<"$issue")
$comments"
  refs="$(dirname "$main")/$(basename "$main")-refs"
  if [ -d "$refs" ]; then
    prompt="$prompt

---

## Reference copies of other Lean projects

Read-only, at the commits named in \`RiemannMasullo/External/SURVEY.md\`, under \`$refs\`:
$(ls "$refs" | sed 's/^/- /')

See \"Using existing Lean\" in AGENTS.md before porting anything from them."
  fi
  if [ -n "$pr" ]; then
    review=$(
      gh api --paginate "$api/issues/$pr/comments" --jq ".[] | select(.author_association | $member) | .body + \"\n\""
      gh api --paginate "$api/pulls/$pr/reviews" --jq ".[] | select((.author_association | $member) and .body != \"\") | .body + \"\n\""
      gh api --paginate "$api/pulls/$pr/comments" --jq ".[] | select(.author_association | $member) | \"\(.path):\(.line // .original_line): \(.body)\n\""
    )
    prompt="$prompt

---

## You are resuming earlier work

This worktree already holds a previous attempt at this issue, which is an open pull request.
Review comments on it:

${review:-(none)}"
  fi
  if [ $dry = 1 ]; then echo "$prompt"; exit 0; fi

  # Claim first: the rest of the setup takes a minute, and `next` must not hand the same issue
  # to two launchers started close together.
  if [ "$role" != scout ] && [ -z "$pr" ]; then
    label --add-label claimed
    note "Claimed by a $role agent ($who) on branch \`$branch\`."
  fi
  if [ -d "$wt" ]; then
    if [ $force = 0 ] && [ -n "$(git -C "$wt" status --porcelain)" ]; then
      echo "worktree $wt has work that was not handed in; run --handin, or --force to discard it" >&2; exit 1
    fi
    git worktree remove --force "$wt"
  fi
  git worktree add -q -B "$branch" "$wt" "$base"
  mkdir -p "$wt/.lake" "$wt/.agent"
  ln -sfn "$main/.lake/packages" "$wt/.lake/packages"   # share the built Mathlib
  # Start from a build of the library, so that only the modules that differ are compiled here.
  # A change low in the import graph rebuilds everything above it, and main moves all the
  # time, so a copy of the main checkout's build is soon stale and every agent started side
  # by side would rebuild the same modules. Instead one shared worktree, "seed", is brought
  # to this agent's starting commit and built under a lock: the first agent pays for what
  # changed, the others copy the result. Lake checks every module against its sources, so a
  # stale or half-written copy costs a rebuild of that module, nothing worse.
  if [ ! -e "$wt/.lake/build" ]; then
    seed="$(dirname "$wt")/seed"; from="$main/.lake/build"
    if [ "$role" != scout ] && [ -z "$pr" ]; then
      (
        flock 8
        start=$(git -C "$wt" rev-parse HEAD)
        if [ ! -d "$seed" ]; then
          git worktree add -q --detach "$seed" "$start" && mkdir -p "$seed/.lake" &&
            ln -sfn "$main/.lake/packages" "$seed/.lake/packages" &&
            { [ ! -d "$main/.lake/build" ] || cp -a --reflink=auto "$main/.lake/build" "$seed/.lake/build"; }
        fi
        git -C "$seed" checkout -q --detach "$start" && (cd "$seed" && lake build RiemannMasullo >/dev/null 2>&1)
        [ ! -d "$seed/.lake/build" ] || cp -a --reflink=auto "$seed/.lake/build" "$wt/.lake/build" 2>/dev/null ||
          rm -rf "$wt/.lake/build"
      ) 8>"$main/.agent/seed.lock" || true
    fi
    if [ ! -e "$wt/.lake/build" ] && [ -d "$from" ]; then
      cp -a --reflink=auto "$from" "$wt/.lake/build" 2>/dev/null || rm -rf "$wt/.lake/build"
    fi
  fi
  printf '%s\n' "$prompt" >"$wt/.agent/PROMPT.md"
  # Record every declaration's signature before the agent touches anything. It is kept outside
  # the worktree so the agent cannot alter it. This also builds the project once for the agent.
  if [ "$role" != scout ] && [ -z "$pr" ]; then
    mkdir -p "$main/.agent/base"
    (cd "$wt" && scripts/signatures.sh) >"$main/.agent/base/$role-$n.txt" 2>"$wt/.agent/base-build.txt" ||
      { echo "could not build the starting point; see $wt/.agent/base-build.txt" >&2; exit 1; }
  fi

  if [ $mode = setup ]; then
    cat <<EOF
Worktree ready: $wt

  cd $wt
  codex$([ "$role" = scout ] && echo ' -c sandbox_workspace_write.network_access=true')        # or: claude
  > Read .agent/PROMPT.md and follow it.

When the agent has finished:

  scripts/agent.sh $role $n --handin
EOF
    exit 0
  fi
fi

# ---- run ----
if [ $mode = all ]; then
  echo "running $cli as $role on #$n in $wt"
  cd "$wt"
  set +e
  case $cli in
    codex)
      args=(exec --sandbox workspace-write -C "$wt" -o "$wt/.agent/last-message.md")
      [ -n "$model" ] && args+=(-m "$model")
      [ -n "$effort" ] && args+=(-c "model_reasoning_effort=\"$effort\"")
      [ "$role" = scout ] && args+=(-c sandbox_workspace_write.network_access=true)
      codex "${args[@]}" "$prompt" </dev/null >"$wt/.agent/log.txt" 2>&1 ;;
    claude)
      args=(-p "$prompt" --permission-mode auto)
      [ -n "$model" ] && args+=(--model "$model")
      claude "${args[@]}" --allowedTools Bash Read Edit Write Grep Glob WebSearch WebFetch </dev/null >"$wt/.agent/log.txt" 2>&1 ;;
    *) echo "unknown cli $cli" >&2; exit 2 ;;
  esac
  echo "agent exited with status $?"
  set -e
fi

# ---- hand in ----
[ -d "$wt" ] || { echo "no worktree at $wt; run --setup first" >&2; exit 1; }
cd "$wt"
git add -A
changed=0; git diff --cached --quiet || changed=1
[ "$role" = scout ] && changed=0

if [ $changed = 1 ]; then
  # Library Lean files only, plus the attribution list, which AGENTS.md asks an agent to extend
  # when it ports a proof from another project.
  stray=$(git diff --cached --name-only | awk '$0 == "RiemannMasullo/External/ATTRIBUTION.md" { next }
    !/^RiemannMasullo\/.*\.lean$/ || /^RiemannMasullo\/External\//')
  [ -z "$stray" ] || fail "A $role agent ($who) changed files its role may not touch. Nothing was pushed.

\`\`\`
$stray
\`\`\`"
  sandboxed bash -c 'scripts/lint.sh && lake build' >"$wt/.agent/build.txt" 2>&1 ||
    fail "A $role agent ($who) stopped with changes that do not pass \`scripts/lint.sh\` and \`lake build\`. Nothing was pushed.

\`\`\`
$(tail -n 25 "$wt/.agent/build.txt")
\`\`\`"
  check="Statement check: not run (no record of the starting point)."
  if [ -s "$main/.agent/base/$role-$n.txt" ]; then
    sandboxed scripts/signatures.sh >"$wt/.agent/signatures.txt" 2>>"$wt/.agent/build.txt"
    diffout=$("$main/scripts/signatures.sh" --compare "$main/.agent/base/$role-$n.txt" "$wt/.agent/signatures.txt") ||
      fail "A $role agent ($who) changed or removed declarations that already existed. Nothing was pushed.

\`\`\`
$diffout
\`\`\`"
    baddefs=$("$main/scripts/signatures.sh" --sorry-in-defs "$wt/.agent/signatures.txt") ||
      fail "A $role agent ($who) left \`sorry\` inside a definition. State the fact as a separate theorem with \`sorry\` and use that theorem in the definition. Nothing was pushed.

\`\`\`
$baddefs
\`\`\`"
    check="Statement check: none of the $(wc -l <"$main/.agent/base/$role-$n.txt") existing declarations changed; $(( $(wc -l <"$wt/.agent/signatures.txt") - $(wc -l <"$main/.agent/base/$role-$n.txt") )) added."
  fi
  title="$role: #$n"; body=""
  if [ -s .agent/PR.md ]; then title=$(head -n 1 .agent/PR.md | sed 's/^#* *//'); body=$(tail -n +2 .agent/PR.md); fi
  [ "$role" = prover ] && link="Closes #$n" || link="Part of #$n"
  git commit -q -m "$title" -m "$link"
  # GitHub now and then rejects a push for no reason of ours ("remote rejected ... (failed)").
  for attempt in 1 2 3; do
    git push -q --force -u origin "$branch" && break
    [ "$attempt" = 3 ] && exit 1
    sleep $((20 * attempt))
  done
  if [ -n "$(pr_number)" ]; then
    echo "updated $(gh pr view "$(pr_number)" --json url --jq .url)"
  else
    gh pr create --base main --head "$head" --title "$title" --body "$body

$link

Written by a $role agent ($who); pushed after \`lake build\` and \`scripts/lint.sh\` passed locally.
$check"
  fi
fi

if [ -s .agent/REPORT.md ]; then
  gh issue comment "$n" --body-file .agent/REPORT.md >/dev/null
  echo "posted report on #$n"
  [ $changed = 1 ] || rel=$(released)
  [ -z "${rel:-}" ] || note "Released."
elif [ $changed = 0 ]; then
  note "$(released)A $role agent ($who) finished without changes or a report."
fi

cd "$main"
# An agent CLI can leave helper processes behind (language servers, tool servers) that keep
# running, and keep a core busy, after it exits. Stop whatever still lives in the worktree.
for pid in $(pgrep -u "$(id -u)"); do
  case "$(readlink "/proc/$pid/cwd" 2>/dev/null)" in "$wt"|"$wt"/*) kill "$pid" 2>/dev/null || true ;; esac
done
mkdir -p .agent/logs   # keep the agent's transcript; the worktree is about to go
for f in log.txt last-message.md build.txt; do
  [ -f "$wt/.agent/$f" ] && cp "$wt/.agent/$f" ".agent/logs/$role-$n.$f"
done
git worktree remove --force "$wt"
echo "done: #$n"
}

main "$@"
