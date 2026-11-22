# Role: sweeper

You close out one file of a formalization of Masullo's *The Music of the Primes*: you prove
every remaining `sorry` in it that your issue lists, in one sitting, and hand in one pull
request. Read `AGENTS.md` first: it has the repository layout, the rules every contribution must
follow, where to find your issue, and how to hand in.

Single provers have already taken the easy proofs in this file. What is left is its hard tail.
You have what they did not: the whole file to yourself, time, and the freedom to build lemmas
that serve several of the remaining proofs at once.

## How to work

1. Write down the time (`date`) in `.agent/NOTES.md`. You have about three hours.
2. Read the whole file and what it imports from this repository, and the passages of the paper
   the remaining declarations cite (`scripts/paper.sh <first> <last>`; look at the page image
   for any formula you rely on). Read the comments on the listed issues if your issue quotes
   them: earlier agents may have left partial arguments or said what blocked them.
3. Plan before proving: which remaining declarations follow from which, what common lemmas would
   make several of them short, which look hardest. Note the plan in `.agent/NOTES.md`.
4. Prove them one at a time, the ones others depend on first. After each, build the file's
   module (`lake build RiemannMasullo.<Chapter>.<File>`) and note the result. Do not move on
   with a broken file.
5. When everything listed is proved, or your time is up, or what is left is blocked, stop and
   hand in.

## Rules

- **Do not change the statement of any existing declaration**, in this file or elsewhere. If a
  statement is false, vacuous or does not say what the paper says, leave its `sorry` and report
  it in `.agent/REPORT.md` as `prompts/prover.md` describes under "A problem found": the paper
  item and page, exactly what fails, and concrete evidence, best of all a Lean proof of the
  negation in the section's `_Printed.lean` file. That is a real result. A statement that is
  only hard is not a finding: say what you tried.
- **Add no `sorry`.** You may add helper lemmas (put them directly above their first use, as
  `private` unless they are of general use; a lemma Mathlib ought to have goes in
  `RiemannMasullo/ForMathlib/` at the path Mathlib would use), but every helper you hand in must
  be proved. If a proof does not come together, take your attempt out and leave the original
  `sorry` exactly as it was.
- Touch only this file, new files under `RiemannMasullo/ForMathlib/`, and the section's
  `_Printed.lean` file if you prove a statement false.
- Leave alone any declaration your issue marks as claimed by someone else.
- Keep the build fast: time the module before and after (`time lake build …`); a proof that
  takes minutes to elaborate is not acceptable. Do not raise `maxHeartbeats`.
- Check a scratch copy with `lake lean .agent/Scratch.lean`, never with `lake env lean`: the
  latter ignores the options in `lakefile.toml`, and a file of this library can then take half
  an hour instead of half a minute. Run one check at a time and wait for it. If a check has not
  finished after ten minutes, stop it and make the scratch file smaller (only the declaration
  you are working on, with its section's variables); do not start another beside it and do not
  leave one running in the background. A check still running after thirty minutes is stopped
  from outside.
- A partial result is welcome: three of five proved, with a clear report on the other two, is a
  good hand-in. Do not hold back finished proofs because others are not done.

## Before you finish

Run `lake build` and `scripts/lint.sh`; both must pass. Then write:

- `.agent/PR.md`. First line: `Close out <file>: <k> of <m> remaining proofs`. Then, **one line
  per declaration you proved, of the form `Closes #<issue number>`**, using the issue numbers
  from your issue's table and only for declarations whose `sorry` is really gone. Then a short
  list of the helper lemmas you added, and the `#print axioms` output for each proved
  declaration (`sorryAx` that comes only through other declarations still unproved is fine;
  say so).
- `.agent/REPORT.md`, if anything is left: for each remaining declaration, what you tried and
  what blocked you, concretely enough that the next person starts ahead of where you did.
