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
   scouting notes in the issue comments.
3. Prove the Lean statement. The paper's argument is your guide, but it is an unrefereed draft: a
   step may be wrong or missing, and a different proof is fine. What counts is the statement on
   `main`, exactly as written.

## Three acceptable results

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

**Blocked.** If the statement is false, vacuous, missing a hypothesis, or rests on a definition
that does not mean what the paper means, do not change it. Write `.agent/REPORT.md` with the
exact problem, a counterexample if you have one, and the corrected statement you would propose.
This is a real result: it tells us something about the formalization or about the paper.

## Where code goes

Put helper lemmas directly above the declaration in the same file. A lemma that is not about the
paper's objects and that Mathlib ought to have goes in `RiemannMasullo/ForMathlib/`, at the path
Mathlib would use. Do not edit the statement of any existing declaration, and do not touch files
outside `RiemannMasullo/`.

## Keep the build fast

A proof that Lean accepts slowly costs everyone: every later build, CI check and agent recompiles
your file and all that imports it. Time the file before and after your change
(`time lake build RiemannMasullo.<Chapter>.<File>` after touching it). If your proof adds more
than about a minute, find the slow step (`set_option profiler true in` on the theorem) and
restructure: usually a unification that has to unfold a large definition or match instances on a
quotient or subtype, which goes away when the argument is stated as a private lemma about
abstract spaces and then applied, or when `exact`/`refine` get explicit arguments and types.
Do not hand in a proof that takes minutes to elaborate, and do not raise `maxHeartbeats` to get
one through.

## Before you finish

Run `lake build` and `scripts/lint.sh`; both must pass. Then write `.agent/PR.md`: a one-line
title, whether the result is proved or split, the new lemmas if any, and the `#print axioms`
output. Keep it short.
