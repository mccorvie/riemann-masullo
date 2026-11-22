# Survey of existing Lean

Scout reports on Lean developments that cover parts of the paper, copied into the repository so
that agents working without network access can read them. They were first posted on
[issue #3](https://github.com/mccorvie/riemann-masullo/issues/3). Every code link fixes the
commit that was inspected. None of this code is vendored; see [`README.md`](README.md) for that
convention and [`ATTRIBUTION.md`](ATTRIBUTION.md) for crediting a ported proof.

Read the report for the part of the paper you are working on:

| Report | Covers |
|---|---|
| [`survey/overview.md`](survey/overview.md) | the first pass over the whole paper: adeles and ideles, Schwartz–Bruhat functions, theta and Poisson, Tate's zeta integral, Haar measure, distributions, bases and nuclear operators, stacks |
| [`survey/arithmetic.md`](survey/arithmetic.md) | Chapters 2–3 and 14, Appendices A–B |
| [`survey/analysis.md`](survey/analysis.md) | functional and harmonic analysis: Chapters 4 and 9, Appendices C–D |
| [`survey/geometry.md`](survey/geometry.md) | quotients, orbits and topological stacks: Chapters 5–8, Appendix E |
| [`survey/trace.md`](survey/trace.md) | orbital shells, integral kernels and the geometric trace: Chapters 10–12 |
| [`survey/endgame.md`](survey/endgame.md) | from the trace identity to zeros: §1.4, §1.8 and Chapter 13 |
| [`survey/prior-formalizations.md`](survey/prior-formalizations.md) | Lean formalizations of RH, Dirichlet GRH and zero-free half-planes for Dedekind zeta and Hecke L-functions, and how their statements relate to this project's targets |

The reports also record problems the scouts noticed in the paper while reading. Those are
readings, not results of the formalization; the ones that have been checked are in
[`ERRATA.md`](../../ERRATA.md).

## Reference copies

The launcher tells each agent where read-only copies of the following projects are, at the
commits the reports cite. Most use other Lean versions, so nothing can be imported; a proof can
be ported with credit. All are Apache-2.0 except `grh`, which is MIT.

| Project | Useful for |
|---|---|
| `algebraic-number-theory-lean` (jonhanke) | Tate's thesis, adelic theta and Poisson, Hecke functional equation, Pontryagin duality, S-units |
| `quadratic-forms-lean` (jonhanke) | adelic Poisson summation for factorizable test functions |
| `FLT` (ImperialCollegeLondon) | Haar measure on the adeles |
| `ideles-journal` (mariainesdff) | ideles and the idele class group |
| `DedekindZetaZeroFree` (AxiomMath) | continuation and a zero-free half-plane for Dedekind zeta; S-integer Poisson summation |
| `hecke-seven-eighths` (Rogerhu12) | continuation and a zero-free half-plane for unitary Hecke L-functions (Appendix B.6) |
| `PrimeNumberTheoremAnd` (AlexKontorovich) | convexity bounds and contour arguments for zeta |
| `gaussian-field` (mrdouglasny) | nuclear spaces, Hermite bases, periodization of Schwartz functions (Chapter 4) |
| `carleson` (fpvandoorn) | maximal functions and covering arguments (Appendix A.5) |
| `AINTLIB` (CBirkbeck) | analytic number theory library |
| `grh` (thatnealpatel, MIT, commit `e55aab2`, same Lean and Mathlib as this project) | Neal Patel's own formalization of parts of the same paper. Mostly over ℚ, with newer all-field material on Hecke characters, finite Euler factors and archimedean factors: real and p-adic logarithmic Fourier terms, the finite Hecke Euler product and its logarithmic derivative on the right half-plane, archimedean Gamma contour terms, Gaussian test functions, the explicit formula for ζ, and rational witnesses for several counterexamples in `ERRATA.md`. The proof issues it bears on carry a note saying which of its files to read. |

Larger projects the reports cite (Tau Ceti, AxiomMath/Stacks, anthropics/fermats-last-theorem,
openai/math, physlib) are not copied locally; ask for one if a section needs it. The Alpöge RH
formalization is published without a license: read its statements for comparison, copy nothing.
