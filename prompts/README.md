# Role prompts

| Role | File | Works on | Output |
|---|---|---|---|
| Integrator | [`integrator.md`](integrator.md) | the whole repository; one long-running session | merges, issues |
| Merger | [`merger.md`](merger.md) | the pull-request queue; one long-running session | merged proofs, reviews of splits |
| Progress tracker | [`progress-tracker.md`](progress-tracker.md) | the public progress map | updated Claude artifact |
| Reviewer | [`reviewer.md`](reviewer.md) | one statement pull request | a review against the paper, posted on the pull request |
| Scout | [`scout.md`](scout.md) | one issue | a comment listing existing Lean and literature |
| Digester | [`digester.md`](digester.md) | one `section` issue | a pull request of statements with `sorry` |
| Prover | [`prover.md`](prover.md) | one `proof` issue | a pull request that proves or splits it |
| Sweeper | [`sweeper.md`](sweeper.md) | every open proof issue of one file | one pull request that closes the ones it proved |

To write or change a prompt here, or `AGENTS.md`, follow [`writing-agents-md.md`](writing-agents-md.md).

Launch scouts, digesters and provers with the launcher. It gives each agent its own worktree
(sharing the built Mathlib), appends the issue to the prompt, and hands in the result:

```sh
scripts/agent.sh prover 42                 # Codex by default
scripts/agent.sh prover next               # oldest unclaimed proof issue
scripts/agent.sh digester 7 --cli claude
scripts/sweep.sh RiemannMasullo/AppB_AnalyticNT/Sec1.lean   # a sweeper: close out one file
scripts/agent.sh scout 7                   # Claude by default
```

To drive an agent yourself in an interactive session, let the launcher do only the setup and the
hand-in:

```sh
scripts/agent.sh prover 42 --setup         # prints the worktree path
cd ../riemann-masullo-wt/prover-42 && codex
#   > Read .agent/PROMPT.md and follow it.
scripts/agent.sh prover 42 --handin        # build, commit, push, open the pull request
```

A scout changes no files, so it can also be started directly in any checkout ("You are the scout
for issue 7; read prompts/scout.md"); it then reads the issue and posts its report with `gh`,
which needs network access (`codex -c sandbox_workspace_write.network_access=true`).

Under Codex's `workspace-write` sandbox an agent in a worktree can build but cannot commit, and
has no network; that is why the launcher does the git and GitHub steps.

The integrator and the merger are started by hand in the main checkout ("You are the merger; read
prompts/merger.md and start"). The merger never touches the working tree there.

Start the progress tracker by hand in the main checkout, in a Claude session with the Artifact
tool. Give it the instruction “You are the progress tracker. Read `prompts/progress-tracker.md`
and start.”

A reviewer is launched with `scripts/review.sh <pull request> --model claude-fable-5-2 --effort xhigh`.
It gets the pull request's files, the paper pages and the digester's report in a scratch
directory, can read the built `main` but change nothing, and its review is posted on the pull
request.

Every agent also reads [`AGENTS.md`](../AGENTS.md), which holds the rules common to all roles.
