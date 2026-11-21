# Contributing

Anyone can contribute, with or without an AI agent. The work is cut into small issues, and most
of them ask for one thing: prove a single Lean declaration whose statement is already written.

## Take an issue

1. Pick an [open `proof` issue that nobody has claimed](https://github.com/mccorvie/riemann-masullo/issues?q=is%3Aissue+is%3Aopen+label%3Aproof+-label%3Aclaimed).
   Each one shows the Lean statement, where it is, and the passage of the paper it comes from.
2. Comment `Claiming` on it. A workflow assigns it to you. If you stop, comment `Releasing` and
   say what blocked you; that note helps whoever takes it next. A claim with no pull request
   after eight hours is released automatically, so that issues do not sit idle; if you are
   still working, just comment `Claiming` again.
3. Fork and clone the repository, then run `lake exe cache get` to download the built Mathlib.
4. Do the work. There are three good outcomes: the declaration is **proved**; it is **split**
   into smaller lemmas that are each left as `sorry`; or you show the statement is **wrong** and
   say so on the issue. The rules are in [`AGENTS.md`](AGENTS.md); the main one is that a proof
   never changes a statement.
5. Open a pull request against `main` with `Closes #<issue>` in the description. CI builds it on
   top of `main` and reports a verdict in the `PR check` run. A finished proof that changes
   nothing else is merged automatically; anything else (a split, a new definition or file,
   statements) waits for the integrator; and if the check fails, its summary says why.

## With a coding agent

Paste this into Codex, Claude Code or any agent that can run shell commands:

> Help formalize a mathematics paper in Lean 4. Fork and clone the repository with
> `gh repo fork mccorvie/riemann-masullo --clone`, run `lake exe cache get` in it, then read
> `AGENTS.md` and `prompts/prover.md`. Choose one open issue labelled `proof` that has no `claimed` or
> `stuck` label, comment `Claiming` on it, and replace that one `sorry` with a proof, without
> changing the statement. Run `lake build` and `scripts/lint.sh`. Then open a pull request
> against `main` whose description says `Closes #<issue>`.

To point it at a particular issue, add "Work on issue #N" to the instruction.

Or let the launcher run the agent in its own worktree and open the pull request for you (it
needs `gh`, `jq`, `bwrap`, and the Codex or Claude Code CLI):

```sh
scripts/agent.sh prover N
```

See [`prompts/README.md`](prompts/README.md) for the other roles and for driving an agent by
hand. You are responsible for what your agent submits: read the diff before you open the pull
request.

## Other ways to help

- **Check a statement.** Compare a Lean statement with the page of the paper it cites. If they
  differ, open an issue describing the difference exactly.
- **Report a gap in the paper.** The manuscript is an unrefereed draft. If an argument does not
  go through, open an issue with the page, what is claimed, and what is missing.
- **Turn a section into statements** (`section` issues). This needs more care than a proof,
  because every later proof depends on it; read [`prompts/digester.md`](prompts/digester.md)
  first.
