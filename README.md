# RiemannMasullo

A Lean 4 formalization of Alessandro Maria Masullo's *The Music of the Primes* (940 pp.), built
in the open by people and their coding agents.

**[Progress map](https://claude.ai/artifact/CtQyX8qfYAF822bgHJHHE3)**: every section of the
paper, what is stated in Lean, what is open as an issue, and what is proved, with the
dependencies between them. It is refreshed about every 20 minutes.

## What this project is for

The paper claims the generalized Riemann hypothesis for the Hecke L-functions of every number
field. It is an unrefereed draft, and its author says it is unfinished. We are formalizing it
from the ground up, as faithfully as we can: each definition and statement goes into Lean as the
paper prints it, with its page number, and every place where the Lean differs from the print is
marked as a deviation.

The aim, in this order:

1. **Formalize as much as possible.** State the paper in Lean section by section, and prove what
   is stated.
2. **Repair as much as possible.** Where a statement is false or a proof does not work, find the
   statement that is true and still does the job the paper needs from it, and prove that.
3. **Identify clearly whatever gaps remain.** What can be neither proved nor repaired is
   recorded exactly: the page, what is claimed, and what is missing.

Every gap or problem found on the way is logged in [`ERRATA.md`](ERRATA.md), each compared with
the printed page. The project does not assume that the paper's main claim is right, and it does
not assume that it is wrong. Its result, whatever becomes of the main theorem, is a
machine-checked account of which parts of the paper hold, which hold after repair, and which do
not.

## Get involved

Several hundred proofs are open, and each one is a single Lean statement that is already
written. You need no special access and no knowledge of the whole paper. Give your coding agent
(Codex, Claude Code or any agent that can run shell commands) this instruction:

> Help formalize a mathematics paper in Lean 4. Fork and clone the repository with
> `gh repo fork mccorvie/riemann-masullo --clone`, run `lake exe cache get` in it, then read
> `AGENTS.md`, `prompts/prover.md` and the section "Working efficiently" of `CONTRIBUTING.md`.
> Pick one library file that has open issues labelled `proof` with no `claimed` or `stuck`
> label, and take several of them, or all of them, from that one file. Comment `Claiming` on
> each. Replace each `sorry` with a proof without changing any statement. Put helper lemmas
> directly above the declaration they serve, as `private theorem`, and edit no other file. While
> you work, build only that file (`lake build RiemannMasullo.<Chapter>.<File>`), after every
> proof. At the end run `lake build` and `scripts/lint.sh`, then open one pull request against
> `main` whose description has one `Closes #<issue>` line per statement you proved. Comment
> `Releasing` on every claimed issue you did not finish, and say what blocked you.

Pick from the [open, unclaimed proofs](https://github.com/mccorvie/riemann-masullo/issues?q=is%3Aissue+is%3Aopen+label%3Aproof+-label%3Aclaimed+-label%3Astuck).
Each issue shows the Lean statement, where it is, and the passage of the paper it comes from. To
point your agent at a particular file or issue, add "Work on `RiemannMasullo/…`" or "Work on
issue #N" to the instruction. (A fork is needed because GitHub only lets collaborators push
branches to this repository; your pull request comes from your copy.)

Doing it by hand works the same way. A proof that is too big can be split into smaller lemmas,
and finding that a statement is wrong is a result too. Every pull request is built and checked
automatically; one that only fills in proofs, and leaves every statement unchanged, is merged
without waiting for anyone. [`CONTRIBUTING.md`](CONTRIBUTING.md) has the details, and what we
have learned about doing this quickly.

## Status

**Active: proving waves 1 and 2, stating the rest of wave 2.** As of 21 November 2026, about
4,700 theorems and 820 definitions are stated in Lean and about 3,950 of the theorems are
proved. Some thirty people have had pull requests merged, about 1,360 pull requests in all.

- **Wave 1** (Appendices A, C and D, Chapters 2–4 and 9) is fully stated, and most of it is
  proved. The remaining proofs are being closed out file by file.
- **Wave 2** (Chapters 5–7 and Appendix B) is being stated section by section, each statement
  reviewed against the paper before it is merged. Appendix B.1–B.6, §5.1–5.3, §6.1–6.2 and §7.1
  are on `main` with their proofs open; §5.4–5.5, §6.3 and §7.2–7.5 follow in dependency order.
- **Wave 3** (Chapters 10–12, the trace formula) has not been started.

Every open `sorry` is an issue that anyone can take. The
[progress map](https://claude.ai/artifact/CtQyX8qfYAF822bgHJHHE3) has the current numbers, and
the roadmap below the order of work.

### What the formalization has found

[`ERRATA.md`](ERRATA.md) has about 200 entries: some 45 statements that are false as printed,
135 that are imprecise, inconsistent or wrongly justified, 16 placeholders or missing pieces,
and 9 reports from readers about parts not yet formalized. Most are in the appendices' and early
chapters' accounts of standard material, and are repaired where they occur: the Lean states the
corrected form and says so.

The second wave has reached the first of the paper's own constructions, and the findings there
weigh more. The printed proof of the structure theorem for the spaces of adelic θ-functions
(Theorem 5.2.1.1) does not work, and whether the theorem holds is being tested in Lean now. The
explicit formulas of §B.4, which Chapter 12 quotes, need their local terms and normalizations
recomputed. None of the entries so far is about the trace formula itself.

### Concerns about the main theorem

Separately from this project, concerns have been raised about gaps in the proof of the paper's
main theorem, the trace formula of Theorem 12.5.1.1. They come from readings of the paper
discussed in the Lean Zulip thread
[Formalising Masullo's proof of GRH](https://leanprover.zulipchat.com/#narrow/channel/113488-general/topic/Formalising.20Masullo.27s.20proof.20of.20GRH/with/642314625),
where the details have not been posted. They did not come from this formalization, which has not
reached that part of the paper. The draft is also unfinished by its author's own account:
Chapter 13, which should deduce GRH from the trace formula, does not yet state its main theorem.

This is what the three aims above are for: when the formalization reaches a part that does not
hold as printed, the work is to repair it if it can be repaired, and otherwise to write down
the gap exactly. How the printed original and its repairs are recorded side by side is still
being worked out. The prerequisites (adeles and ideles, Haar measures, locally convex and
nuclear spaces, Schwartz–Bruhat functions) are standard mathematics worth having in Lean
whatever becomes of the main theorem.

## The paper

The manuscript is in [`paper/`](paper/) (PDF plus a `pdftotext -layout` extraction for search),
and [`transcription/`](transcription/README.md) has a Markdown transcription with the formulas
in LaTeX, contributed by [@aadrianvv](https://github.com/aadrianvv): a reading aid, checked
against the PDF but not an exact copy. The PDF decides.

## Layout

The library mirrors the paper's table of contents. Each chapter or appendix has an index file,
and its sections go in a directory of the same name (`RiemannMasullo/Ch02_AdelicTheta/Sec1.lean`):

| File | Paper |
|---|---|
| `RiemannMasullo/Ch02_AdelicTheta.lean` | Ch. 2 Adelic θ-functions |
| `RiemannMasullo/Ch03_IdelicZeta.lean` | Ch. 3 Idelic Zeta Functions |
| `RiemannMasullo/Ch04_PeriodicSchauderBases.lean` | Ch. 4 Periodic Schauder Bases on modulated groups |
| `RiemannMasullo/Ch05_ThetaZSpaces.lean` | Ch. 5 Spaces of adelic θ-functions and Idelic Z-functions |
| `RiemannMasullo/Ch06_LocalGlobal.lean` | Ch. 6 Local-Global structures |
| `RiemannMasullo/Ch07_SchauderBasesZeta.lean` | Ch. 7 Schauder Bases of Idelic Zeta functions |
| `RiemannMasullo/Ch08_PeriodicOrbits.lean` | Ch. 8 Periodic Orbits and Fixed Points |
| `RiemannMasullo/Ch09_HardySobolev.lean` | Ch. 9 Hardy-Sobolev topologies |
| `RiemannMasullo/Ch10_TraceSpectral.lean` | Ch. 10 Trace formula: Spectral Side |
| `RiemannMasullo/Ch11_ShellStructure.lean` | Ch. 11 The Shell Structure |
| `RiemannMasullo/Ch12_TraceGeometric.lean` | Ch. 12 Trace formula: Geometric Side |
| `RiemannMasullo/Ch13_ZerosHecke.lean` | Ch. 13 Zeros of Hecke L-functions |
| `RiemannMasullo/Ch14_Complements.lean` | Ch. 14 Complements |
| `RiemannMasullo/AppA_AlgebraicNT.lean` | App. A Algebraic Number Theory |
| `RiemannMasullo/AppB_AnalyticNT.lean` | App. B Analytic Number Theory |
| `RiemannMasullo/AppC_LCTVS.lean` | App. C Locally convex TVS |
| `RiemannMasullo/AppD_SchwartzBruhat.lean` | App. D Schwartz-Bruhat functions |
| `RiemannMasullo/AppE_TopologicalStacks.lean` | App. E Topological stacks |

(Chapter 1 is the informal introduction and has no file.)

Third-party formalizations we build on are vendored under
[`RiemannMasullo/External/`](RiemannMasullo/External/README.md); nothing is vendored yet.

## Roadmap

The order follows the paper's own cross-references. Two streams run in parallel and meet at the
trace formula:

| Wave | Paper | Status |
|---|---|---|
| 1 | Appendices A.1–A.3, A.5, C, D; then Chapters 2–3 (adelic θ-functions, idelic zeta functions) and, independently, Chapters 4 and 9 (periodic Schauder bases, Hardy–Sobolev spaces) | all stated; most proofs done, the rest being closed out file by file: [open proof issues](https://github.com/mccorvie/riemann-masullo/issues?q=is%3Aissue+is%3Aopen+label%3Aproof+-label%3Aclaimed) |
| 2 | Chapters 5–7, with Appendix B.1–B.6 | Appendix B.1–B.6, §5.1–5.3, §6.1–6.2 and §7.1 stated, proofs open; the remaining [section issues](https://github.com/mccorvie/riemann-masullo/issues?q=is%3Aissue+is%3Aopen+label%3Asection) (§5.4–5.5, §6.3, §7.2–7.5) are being stated in dependency order |
| 3 | Chapters 10–12: the trace formula | not yet seeded |
| later | Chapters 8 and 14, Appendix E, A.4, B.7 | only when something needs them |

An issue labelled `blocked` is waiting for the sections it builds on. The appendices are mostly
standard mathematics, and several pieces already exist in other Lean projects (see
[issue #3](https://github.com/mccorvie/riemann-masullo/issues/3)); the chapters are where the
paper's own argument is tested.

## How the work is organized

Work goes through issues and pull requests: scouts find existing Lean, digesters turn paper
sections into statements, reviewers compare those statements with the paper, provers and
sweepers close the `sorry`s, and an integrator and a merger review and merge. Start with
[`CONTRIBUTING.md`](CONTRIBUTING.md); the rules every contribution follows are in
[`AGENTS.md`](AGENTS.md), and the role prompts in [`prompts/`](prompts/README.md).

## Building

```sh
lake exe cache get   # download prebuilt Mathlib
lake build
```

Pinned to Lean `v4.36.0` / Mathlib `v4.36.0`.

## Comparator

The target statements are checked with [Comparator](https://github.com/leanprover/comparator)
(`lake comparator`, built into Lean from 4.35), following the setup for Alpoge's formalization at
<https://github.com/Deicyde/riemann-hypothesis>.

| File | What it is |
|---|---|
| [`Statements.lean`](Statements.lean) | definitions of the target statements; imports only Mathlib |
| [`Challenge.lean`](Challenge.lean) | the theorems, with `sorry` |
| [`Main.lean`](Main.lean) | the same theorems, to be proved from `RiemannMasullo` |
| [`comparator.json`](comparator.json) | the Comparator config |

| Theorem | Statement |
|---|---|
| `riemannHypothesis` | Mathlib's `RiemannHypothesis` |
| `riemannZeta_eq_zero_re`, `LFunction_ne_zero_of_half_lt_re`, `LFunction_eq_zero_re`, `LFunction_eq_zero_re_of_isPrimitive` | RH and GRH for Dirichlet L-functions, identical to the Alpoge challenge |
| `dedekindZeta_zeros_re` | GRH for the Dedekind zeta function of every number field |
| `heckeLFunction_zeros_re` | GRH for `L(s, χ)`, every number field, every unitary Hecke character |

```sh
lake comparator              # needs bubblewrap; add --paranoid for the extra kernels
```

It currently rejects with `Illegal axiom detected: 'sorryAx'`, as it should until `Main.lean` has
no `sorry`.

The paper's own main theorem (Theorem 13.3.1.2) is a placeholder in the current draft, so the last
two statements were reconstructed from the introduction and have not been reviewed.

## License

The Lean code and everything else written for this project is released under the
[Apache License 2.0](LICENSE), the license of Mathlib. The manuscript in [`paper/`](paper/README.md)
belongs to its author and is not covered by it. Code vendored under `RiemannMasullo/External/`
keeps its own license and notices.
