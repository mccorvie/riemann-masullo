import Statements
import RiemannMasullo.Ch13_ZerosHecke.Targets

/-!
# Solution

The same theorems as `Challenge.lean`, each obtained from the library. Comparator rejects this
file for as long as anything it rests on contains `sorry`.

The route is: the trace formula of Chapter 12 (`RiemannMasullo/Ch12_TraceGeometric/Sec5.lean`),
then the argument of §1.4 of the paper, which ends in the paper's main claim
`RiemannMasullo.heckeL_zero_re_eq_half` (`RiemannMasullo/Ch01_Introduction/Sec4.lean`), then
the classical comparisons with Mathlib's L-functions in
`RiemannMasullo/Ch13_ZerosHecke/Targets.lean`, which state these seven theorems. What is still
open on that route, and what is known to fail, is recorded in `ERRATA.md`.
-/

/-- The headline claim, stated with Mathlib's definition only. -/
theorem riemannHypothesis : RiemannHypothesis := RiemannMasullo.riemannHypothesis

theorem riemannZeta_eq_zero_re : RiemannZetaZerosOnLine := RiemannMasullo.riemannZeta_eq_zero_re

theorem LFunction_ne_zero_of_half_lt_re : DirichletLNonvanishingRightOfHalf :=
  RiemannMasullo.LFunction_ne_zero_of_half_lt_re

theorem LFunction_eq_zero_re : DirichletLZerosOnLine := RiemannMasullo.LFunction_eq_zero_re

theorem LFunction_eq_zero_re_of_isPrimitive : PrimitiveDirichletLZerosOnLine :=
  RiemannMasullo.LFunction_eq_zero_re_of_isPrimitive

theorem dedekindZeta_zeros_re : DedekindZetaZerosOnLine := RiemannMasullo.dedekindZeta_zeros_re

theorem heckeLFunction_zeros_re : HeckeLZerosOnLine := RiemannMasullo.heckeLFunction_zeros_re
