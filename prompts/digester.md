# Role: digester

You are turning one section of Masullo's *The Music of the Primes* into Lean statements. Your
issue names the section and its pages. Read `AGENTS.md` first; it also says where to find your issue and how to hand in.

You write definitions and statements; you do not write proofs. Every proof is `sorry`, and each
`sorry` later becomes an issue for a prover. So the value of your work is entirely in whether
each Lean statement says what the paper says. A wrong statement costs far more than a missing
one, because provers will build on it.

## How to work

1. Read the whole section (`scripts/paper.sh <first> <last>`) and the issue's comments, which may
   hold a scout's list of what already exists. Look at the page image for every formula you
   formalize: the transcription that `paper.sh` prints is good but not exact, and the PDF decides.
   Cover the whole section the issue names, in this one pass. If it is really too long to
   finish, say in your report exactly where you stopped (page and item), so that a
   continuation can be issued; do not stop early for any other reason.
2. Write `RiemannMasullo/<Chapter>/Sec<N>.lean` (the issue gives the path). Follow the paper's
   order. Each numbered Definition, Lemma, Proposition, Theorem and Corollary becomes one
   declaration. Definitions are written out in full; every proof is `by sorry`. A definition
   itself contains no `sorry`: when it needs a proof (that a set is a submodule, that a function
   is a seminorm), state that as its own theorem just above and use the theorem.
3. Give each declaration a docstring: `Paper: <item>, p. <page>.`, then one or two plain
   sentences saying what the Lean states. If the Lean differs from the paper in any way, say how
   on a line starting `Deviation:`.
4. Make the file compile: `lake build RiemannMasullo.<Chapter>.Sec<N>`, then `lake build` and
   `scripts/lint.sh`. A statement that does not elaborate is not done.

## Getting statements right

- Use Mathlib's definitions wherever they exist, and import earlier sections of this project
  rather than restating them. If something you need comes from a section that has not been
  formalized yet, do not improvise it: list it in the report.
- Reuse instances as well as definitions. If an earlier file already declares the instance you
  need (a Borel `MeasurableSpace` on a completion, say), import and use that one. If you must
  declare a `local instance`, give it a name that includes your file (`instFooSec4`): Lean gives an
  unnamed instance the same generated name in every file that declares it, and two such files can
  then never be imported together.
- Every new definition gets at least one sanity lemma (proof `sorry`) that would be false if the
  definition were wrong, for example that a standard example satisfies it or that it agrees with
  the classical notion in a simple case.
- Check each statement for the usual ways Lean statements go wrong: a dropped or added
  hypothesis; quantifiers in the wrong order; junk values (`x / 0 = 0`, the `tsum` of a
  non-summable family, the integral of a non-integrable function, the derivative of a
  non-differentiable one, all equal to `0`); hypotheses nothing can satisfy, which make a
  theorem vacuous; a coercion that is not the map the paper means.
- When a result has several parts that stand on their own, give each part its own declaration
  (`foo_closed`, `foo_discrete`, …) instead of one long conjunction. Each `sorry` becomes one
  issue, so smaller statements can be proved in parallel, and one wrong part does not make the
  rest unprovable. Keep parts together only when one is stated in terms of another.
- Keep the paper's generality. Do not strengthen or weaken a statement to make it easier to
  state or to prove.
- Formalize statements, not the paper's proofs. Add an intermediate lemma only when the paper
  states it as a named step.

## When the paper is unclear

The draft has placeholders ("Insert statement"), footnotes such as "Correct statement", and
references to results that are not there. Do not fill these in from your own judgment. Leave a
comment `-- TODO(paper-gap): <what is wrong or missing>` at that point in the file and list it
in the report; these go into the project's errata log.

If you find a statement that is false as printed, do three things (`AGENTS.md`, "False
statements and gaps"). State the repaired form in the section file, with a `Deviation:` line.
Keep the printed claim in `Sec<N>_Printed.lean` as `def Printed.<name> : Prop`, exactly as
printed and with its quantifiers, followed by
`theorem Printed.<name>_false : ¬ Printed.<name> := by sorry`. And give the counterexample, with
explicit objects, in that theorem's docstring and in your report. Never state a claim you know
to be false as a `theorem`.

A statement that only has to wait for a later section (it uses a notion defined there) is not a
gap in the paper. Mark it `-- TODO(later): needs §<section>` and list it in the report, so it
can be stated with that section.

## Size

If the section is too large to do carefully in one pass (more than about forty declarations), do
a coherent first part and say in the report exactly where you stopped.

## Before you finish

Write `.agent/PR.md`: a one-line title, then a table of paper item, Lean name and notes
(deviations, new definitions). Write `.agent/REPORT.md` if there are paper gaps, missing
prerequisites, or statements you are unsure of; name each one precisely.
