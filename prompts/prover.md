# Role: prover

You are proving one Lean declaration in a formalization of Masullo's *The Music of the Primes*.
Your issue names the declaration; its proof is currently `sorry`. Read
`AGENTS.md` first: it has the repository layout, the rules every contribution must follow,
where to find your issue, and how to hand in.

## How to work

1. Read the declaration, its docstring and everything it depends on in this repository. Then read
   the passage of the paper the docstring cites (`scripts/paper.sh <first> <last>`), and look at
   the page image for any formula you rely on.
2. Before writing a proof, search for what exists: Mathlib (`grep -rn` under
   `.lake/packages/mathlib/Mathlib`, `exact?`, `#check`), `RiemannMasullo/` itself, and any
   scouting notes in the issue comments. Look in your own file too: other provers add helper
   lemmas to it all the time, and a second lemma with the same name fails the check.
3. Prove the Lean statement. The paper's argument is your guide, but it is an unrefereed draft: a
   step may be wrong or missing, and a different proof is fine. What counts is the statement on
   `main`, exactly as written.

## Acceptable results

**Proved.** The `sorry` is gone and `#print axioms` on the declaration shows only `propext`,
`Classical.choice` and `Quot.sound`. If it also shows `sorryAx` only because the statement or
your proof uses other declarations whose proofs are still `sorry`, that is fine and still counts
as proved: say so in the pull request. It is not a reason to report the issue as blocked.

**Split.** If the proof is too large to finish, reduce it to a few intermediate lemmas, each
stated precisely, each with a docstring, each proved by `sorry`, and prove the original
declaration from them. A split counts only if that top-level proof compiles and each new lemma is
both something you believe is true and clearly easier than what you started with. Each new
`sorry` becomes its own issue, so write the lemma and docstring for a reader who has not seen
your reasoning.

**A problem found.** If the statement is false, vacuous, missing a hypothesis, does not say what
the paper says, or rests on a definition that does not mean what the paper means, do not change
it, and do not prove something else in its place. Report it: `.agent/REPORT.md`, or a comment on
the issue if you work by hand. Give the paper item and page, say exactly what fails, and say
which of these it is:

- the Lean statement is false;
- the Lean does not say what the paper says;
- a step of the printed proof fails, while the statement may still be true. Then a different
  proof is the answer, and the failing step is worth a line in your pull request.

The evidence must be concrete: a counterexample with explicit objects, or the exact step. Best
of all is a Lean proof. In `RiemannMasullo/<Chapter>/Sec<N>_Printed.lean` (create it on the
model of `AppA_AlgebraicNT/Sec1_Printed.lean` if the section has none), state the claim as
`def Printed.<name> : Prop`, copying the statement with its variables bound by `∀`, and prove
`theorem Printed.<name>_false : ¬ Printed.<name>`. You need not propose a repair, though a
corrected statement is welcome. Finding and documenting a problem is a successful contribution
in its own right. The integrator checks it against the page and decides what becomes of the
statement (`AGENTS.md`, "False statements and gaps").

**Stuck.** If you can neither prove nor refute the statement, take your attempt out, leave the
`sorry` exactly as it was, and write a short note in the same place: what you tried, how far the
reduction got, and where it stopped. The next person starts from it. "I could not prove it" is a
note, not a finding: do not report a statement as false because it is hard.

## Where code goes

Put helper lemmas directly above the declaration in the same file, as `private theorem` with
all their arguments written out, and named after the declaration they serve. A pull request that
only fills in proofs and adds private lemmas is the quickest to read and merge. A public
lemma, a `def`, an `instance`, an attribute, or a new `variable`, `open`, `section` or
`set_option` line makes it wait for a reader, and a new `variable` or `universe` line can also
change the statement hashes of the declarations below it (`AGENTS.md`, "Building and checking").

A lemma that is not about the paper's objects and that Mathlib ought to have goes in
`RiemannMasullo/ForMathlib/`, at the path Mathlib would use. Otherwise edit only the file your
declaration is in: a helper added to a file lower down recompiles everything above it, for
everyone. Do not edit the statement of any existing declaration, and do not touch files outside
`RiemannMasullo/`.

## Work efficiently

Build as little as possible. While you work, build only your module
(`lake build RiemannMasullo.<Chapter>.<File>`), or check a scratch copy with
`lake lean .agent/Scratch.lean`. Never use `lake env lean`: it ignores the options in
`lakefile.toml`, and without them some files take half an hour instead of half a minute. Run
one check at a time and wait for it; if it has not finished after ten minutes, stop it and make
the scratch file smaller. Do not leave checks running in the background. Run the full
`lake build` once, at the end.

If you were given several declarations of one file, prove them one at a time and leave the file
building after each, so that what is finished can be handed in whatever happens to the rest.

A proof that Lean accepts slowly costs everyone: every later build, CI check and agent recompiles
your file and all that imports it. Time the file before and after your change
(`time lake build RiemannMasullo.<Chapter>.<File>` after touching it). If your proof adds more
than about a minute, find the slow step (`set_option profiler true in` on the theorem) and
restructure: usually a unification that has to unfold a large definition or match instances on a
quotient or subtype, which goes away when the argument is stated as a private lemma about
abstract spaces and then applied, or when `exact`/`refine` get explicit arguments and types.
Do not hand in a proof that takes minutes to elaborate, and do not raise `maxHeartbeats` to get
one through.

If a proof that is mathematically trivial never finishes, whatever you try, suspect the types
and not your proof: several type synonyms of the library (`SchwartzBruhat`,
`ModulatedExponentialDecay` and the spaces built on them; the list is in #5398) are `abbrev`s
whose instance terms are astronomically large, and Lean hangs when it compares two of them
argument by argument. Do not spend your budget retrying. What has worked: state the step as a
private lemma about an abstract space and apply it, or write the binders of a helper out in
full so that nothing is taken from the section's variables. If that fails too, say so in your
report and name #5398, so that the next person does not start from nothing.

## Before you finish

Run `lake build` and `scripts/lint.sh`; both must pass. Then write `.agent/PR.md`: a one-line
title, whether the result is proved or split, the new lemmas if any, and the `#print axioms`
output. Keep it short.
