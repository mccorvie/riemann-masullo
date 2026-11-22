# Contributing

Anyone can contribute, with or without an AI agent. The project formalizes Masullo's *The Music
of the Primes* from the ground up, as faithfully as it can, and logs every gap or problem it
finds in [`ERRATA.md`](ERRATA.md). The aim is to formalize as much as possible, then repair as
much as possible, then say clearly what gaps remain (see the [README](README.md)).

The work is cut into small issues, and most of them ask for one thing: prove a single Lean
declaration whose statement is already written.

## With a coding agent

Paste this into Codex, Claude Code or any agent that can run shell commands:

> Help formalize a mathematics paper in Lean 4. Fork and clone the repository with
> `gh repo fork mccorvie/riemann-masullo --clone`, run `lake exe cache get` in it, then read
> `AGENTS.md`, `prompts/prover.md` and the section "Working efficiently" of `CONTRIBUTING.md`.
> Pick one library file that has open issues labelled `proof` with no `claimed` or `stuck`
> label, and take several of them, or all of them, from that one file. Comment `Claiming` on
> each. Try to prove each statement as written. A different proof from the paper's is welcome,
> and a proof that is too large can be split into smaller, precise lemmas as the prover guide
> says. Never change a statement. If you find a counterexample, a mismatch between the Lean and
> the manuscript, or a specific gap in the printed argument, report it on the issue instead:
> give the paper item and page and say exactly what fails, with a concrete counterexample or the
> failing step, best of all as a Lean proof of the negation. That is a successful contribution
> in its own right, and you need not propose a repair. If you can neither prove nor refute a
> statement, leave a short note on the issue saying what you tried and where you got stuck. Put
> helper lemmas directly above the declaration they serve, as `private theorem`, and edit no
> other file. While you work, build only that file
> (`lake build RiemannMasullo.<Chapter>.<File>`), after every proof. At the end run `lake build`
> and `scripts/lint.sh`, then open one pull request against `main` whose description has one
> `Closes #<issue>` line per statement you proved. Comment `Releasing` on every claimed issue
> you did not finish.

To point it at a particular file or issue, add "Work on `RiemannMasullo/…`" or "Work on issue
#N". You are responsible for what your agent submits: read the diff before the pull request is
opened.

Or let the launcher run the agent in its own worktree and open the pull request for you (it
needs `gh`, `jq`, `bwrap`, and the Codex or Claude Code CLI):

```sh
scripts/agent.sh prover N
```

[`prompts/README.md`](prompts/README.md) describes the other roles and how to drive an agent by
hand.

## By hand

1. Pick an [open `proof` issue that nobody has claimed](https://github.com/mccorvie/riemann-masullo/issues?q=is%3Aissue+is%3Aopen+label%3Aproof+-label%3Aclaimed+-label%3Astuck+-label%3Agap).
   Each one shows the Lean statement, where it is, and the passage of the paper it comes from.
   Better still, pick a file and take several of its issues (see below).
2. Comment `Claiming` on each issue you take. A workflow assigns it to you. If you stop, comment
   `Releasing` and say what blocked you; that note is handed to whoever takes it next. A claim
   with no pull request after eight hours is released automatically, so that issues do not sit
   idle; if you are still working, comment `Claiming` again.
3. Fork and clone the repository, then run `lake exe cache get` to download the built Mathlib.
4. Do the work. There are three good outcomes: the declaration is **proved**; it is **split**
   into smaller lemmas that are each left as `sorry`; or you show the statement is **wrong** and
   say so on the issue. The rules are in [`AGENTS.md`](AGENTS.md); the main one is that a proof
   never changes a statement.
5. Open a pull request against `main` with one `Closes #<issue>` line per statement.

## What happens to your pull request

The `PR check` run builds your change on top of the current `main` and gives one of four
verdicts. Its summary says why.

| Verdict | Meaning | What happens |
|---|---|---|
| merge | It builds, passes the lint, leaves every existing statement as it was, and only fills in proofs and adds private lemmas in existing files. | Merged automatically, usually within minutes. |
| read | It passes, but does something a person should look at: a split (new `sorry`s), a new definition or file, a public lemma, a statement. | Waits for the merger or the integrator. |
| fail | It does not merge into `main`, build, pass the lint, or keep the existing statements. | Yours to fix; the merger usually comments with what is wrong. |
| error | The check itself could not run. | It says nothing about your change. If it stays that way, say so on the pull request. |

A pull request that was returned with a comment and never picked up again is the main way
finished work gets lost here. Look at yours again after the check.

## Working efficiently

This is what the project's first days, with many people and agents working at once, have
taught us. None of it is required, but all of it was learned the slow way.

### Take a file, not an issue

- **Take several related issues from one file, or all of them, in one pull request.** The
  proofs of a file share its definitions, notations and helper lemmas, so the reading is done
  once. It is also one check instead of many, and your own pull requests cannot collide with
  each other. Our best results come from "sweeps": one agent with a strong model and a budget of
  a few hours takes every open proof of a file, proves them one at a time, builds after each,
  and hands in a single pull request. Sweeps handed in about 240 proofs in their first four
  hours. (Project members start one with `scripts/sweep.sh <file>`, which needs write access to
  label the issues; from a fork, the instruction above does the same thing.)
- Claim every issue before you start, and put one `Closes #<issue>` line per proved statement in
  the description. Release the ones you did not finish, with a note on what you tried.
- **Prefer a file that is low in the import order and nearly finished.** Once a file has no
  `sorry` left, nobody edits it again, and everything that imports it stops being rebuilt. The
  [progress map](https://claude.ai/artifact/CtQyX8qfYAF822bgHJHHE3) shows what each file has left.
- Do not crowd a file. If two or three other people have claims or open pull requests in it,
  choose another; the same lines and the same helper lemmas will collide.
- An agent working through a file should keep notes as it goes and leave the file building
  after every proof. Then an interrupted run can be resumed, and a partial run still hands in
  what it proved.

### Build as little as possible

Lake rebuilds a file when it, or anything it imports, has changed, and then rebuilds everything
that imports it. What an edit costs is decided by how much of the library sits above the file.

- Run `lake exe cache get` once. If `lake build` ever starts compiling Mathlib's own files,
  stop: the setup is off. Never run `lake update`.
- While you work, build only your module: `lake build RiemannMasullo.<Chapter>.<File>`. Run the
  full `lake build` once, before you open the pull request. A full build from nothing takes CI
  about twenty minutes; after that it is incremental.
- For a single file or a scratch file use `lake lean path/to/File.lean`, never `lake env lean`.
  Only the former applies the options in `lakefile.toml`. One of them turns off a linter that
  otherwise makes some files take half an hour instead of half a minute.
- **Edit only the file your issues are in.** A helper lemma added to a file lower down
  recompiles everything above it: for you now, and for every contributor and every check once
  it is merged. Put helpers directly above the declaration that needs them. A lemma that Mathlib
  ought to have goes under `RiemannMasullo/ForMathlib/`, at the path Mathlib would use.
- Do not merge `main` into your branch more often than you need to. Each time, the files that
  changed below yours are rebuilt. The check builds your change on top of the current `main`
  anyway, so a branch that is behind but has no conflict is fine.
- Do not pull, switch branches or run a second build in a checkout where a build or a script is
  running. Use a second worktree.

### Keep the file fast

A proof that Lean accepts slowly is paid for by every later build, check and agent. Twice, one
file went from about a minute to over half an hour, and everything slowed down until it was
found.

- Time your module before and after your change. If your proof adds more than about a minute,
  find the slow step with `set_option profiler true in` on the theorem.
- The usual cause is a unification that unfolds a large definition, or matches instances
  through a quotient or a subtype. It goes away when the argument is stated as a private lemma
  about abstract spaces and then applied, or when `exact` and `refine` get explicit arguments
  and types.
- Do not raise `maxHeartbeats` to get a proof through.

### Get merged without waiting

The automatic merge decides from the text of your change whether it is "only proofs". To stay
on that path:

- Write helpers as `private theorem` or `private lemma`, with all their arguments written out.
  A public lemma, a `def`, an `instance`, an attribute such as `@[simp]`, a notation, or a new
  `variable`, `open`, `section` or `set_option` line sends the pull request to a reader.
  (`open … in` and `set_option linter.… false in` directly before a theorem are fine, and so is
  an `import` of a Mathlib or library module.)
- A split is welcome, but a new `sorry` is always read by a person, and so is a new file.
- Compare statements before and after with `scripts/signatures.sh` (see `AGENTS.md`). If it
  lists a declaration you did not touch, a helper above it has renamed its universe parameters;
  `AGENTS.md` says how to avoid that.
- `sorryAx` in `#print axioms` is fine when it comes from other declarations that are still
  unproved. It is not a reason to report an issue as blocked.

### Avoid collisions

`main` moves every few minutes.

- Open the pull request as soon as it builds. A branch that waits for hours meets conflicts,
  most often in the `import` block at the top of the file.
- Before you add a helper lemma, search the current `main` for it. Useful small facts get
  proved twice, and the second pull request then fails on a duplicate name. Name a helper after
  the declaration it serves.
- Leave "Allow edits by maintainers" ticked on your pull request, so that the merger can bring
  your branch up to date for you.

### Running several agents

- Give each agent its own checkout (`git worktree add`), and never run two builds in one. Share
  the downloaded Mathlib by linking `.lake/packages`, and start each new worktree with a copy of
  an up-to-date `.lake/build` (`cp -a --reflink=auto`). Otherwise every agent spends its first
  twenty minutes rebuilding the library. `scripts/agent.sh` does all of this.
- More agents is not more throughput. A build uses every core, and the checks share a queue.
  When ours were saturated, a check took over an hour; running fewer agents got more merged.
- Start unattended agents with an empty standard input (`</dev/null`). Nine of ours once sat
  for two hours waiting on an input that nobody was going to type.
- Never print a raw term (`repr` of an `Expr`): it has used over 70 GB of memory for a single
  statement, twice. A `lean` process that grows to tens of gigabytes is a bug; stop it.

## When the paper is wrong

The manuscript is an unrefereed draft, and finding where it does not hold is part of the job.
Finding and documenting a problem is a successful contribution in its own right, and you need
not propose a repair.

- **Report it on the issue**: the paper item and page, and exactly what fails. Say which it is:
  the Lean statement is false; the Lean does not say what the paper says; or a step of the
  printed proof fails. In the last case the statement may still be true, and a different proof
  is welcome.
- **Bring evidence**: a counterexample with explicit objects, or the exact step that fails. Best
  of all is a Lean proof of the negation, handed in as a pull request ([`AGENTS.md`](AGENTS.md),
  "False statements and gaps", says where it goes). "I could not prove it" is a useful note for
  the next person, but it is not a finding.
- **Do not change the statement**, and do not prove something else in its place. The integrator
  checks the report against the page, decides what becomes of the statement, and logs it in
  [`ERRATA.md`](ERRATA.md).
- **If you can neither prove nor refute it**, leave a short note on the issue saying what you
  tried and where it stopped, and release it.

What happens then:

| Finding | In the Lean |
|---|---|
| Our Lean misreads the paper | The statement is corrected, and the issue shows the new text. |
| The printed statement is false | The printed claim is kept as a proposition, `Printed.<name>`, with a theorem that proves its negation. The repaired statement stands next to it under the ordinary name. |
| The printed proof fails, the statement is plausible | Nothing changes; the note stays on the issue. |
| Nobody can prove or refute it | It becomes a recorded gap: a named theorem left as `sorry`, labelled `gap`, with everything else proved around it. |

Before you rely on a formula, look at the page image (`scripts/paper.sh --png <page>`). The
transcription is a reading aid; the PDF decides.

## Other ways to help

- **Check a statement.** Compare a Lean statement with the page of the paper it cites. If they
  differ, open an issue describing the difference exactly.
- **Report a gap in the paper.** If an argument does not go through, open an issue with the
  page, what is claimed, and what is missing.
- **Turn a section into statements** (`section` issues). This needs more care than a proof,
  because every later proof depends on it; read [`prompts/digester.md`](prompts/digester.md)
  first.
