module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Tactic.NormNum

/-! # Numerical bounds for the reversed rational shell calculation

These exact rational inequalities certify the frequency-band and prime-power
estimates for the test with log profile proportional to `t^35 * exp (-8 * t)`.
This file is an isolated leaf of the development.
-/

public section

namespace RiemannMasullo.Isolated

/-- Paper: (11.3.2.4), p. 496, with the projection order of Definition 10.4.3.7, p. 473.
The central frequency envelope, the boundary coefficient factor and the tail
series give the rational numerical estimates used for the reversed shell.
Reconstruction: These inequalities certify the constants in the rational
zero-width counterexample. The operator estimates are separate. -/
theorem retainedShell_reversed_trace_constants :
    2 * (∑ j ∈ Finset.range 13,
      ((17 + j : ℚ) ^ 2 * (11 / 4 : ℚ) ^ (2 * (j + 1))) /
        (1 + (j : ℚ) ^ 2 / 64) ^ 36) < (304 : ℚ) ^ 2 ∧
    (10 : ℚ) ^ 6 < (27 / 10 : ℚ) ^ 14 ∧
    (4 : ℚ) * (501 / 1000) * 55 * 304 / 10 ^ 6 < 17 / 500 ∧
    (640 : ℚ) * (4 / 13) ^ 18 * (197 + 4 * (144 + 1728 / 21)) < 1 / 1000 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · norm_num [Finset.sum_range_succ]
  · norm_num
  · norm_num
  · norm_num

/-- Paper: (11.3.2.5), p. 496.
The three gamma-density samples and their half-shifted weights give the
rational lower bound for the orbital trace used in the reversed shell test.
Reconstruction: The samples are bounded below at log norms 27/8, 33/8 and
39/8 using the upper bound 68/25 for the exponential of one. -/
theorem retainedShell_reversed_orbital_constants :
    (17 / 100 : ℚ) < (8 : ℚ) * 27 ^ 35 / ((Nat.factorial 35 : ℚ) * (68 / 25) ^ 27) ∧
    (49 / 100 : ℚ) < (8 : ℚ) * 33 ^ 35 / ((Nat.factorial 35 : ℚ) * (68 / 25) ^ 33) ∧
    (40 / 100 : ℚ) < (8 : ℚ) * 39 ^ 35 / ((Nat.factorial 35 : ℚ) * (68 / 25) ^ 39) ∧
    (21 / 250 : ℚ) < (69 / 100) *
      ((17 / 100) / 6 + (49 / 100) / 8 + (40 / 100) / 12) := by
  norm_num [Nat.factorial]

/-- Paper: (11.3.2.4)–(11.3.2.5), p. 496.
The rational upper bound for the surplus derivative contribution is inside
the margin between the line trace norm and half the orbital value.
Reconstruction: The first inequality bounds the zero-count majorant for the
gamma-density prototype. The second allows for compact smoothing of that test. -/
theorem retainedShell_positiveWidth_constants :
    (4 : ℚ) * (16 / 65) ^ 18 * (196 + 14 ^ 3 / 21) < 1 / 10 ^ 7 ∧
    (2 : ℚ) * (9 / 250 + 1 / 1000) < 21 / 250 := by
  norm_num

/-- Paper: (11.3.2.4)–(11.3.2.5), p. 496, and the polar subtractions on p. 520.
The zero-width central bands, the outer bands and the surplus derivative cost
for the test that annihilates both polar Mellin values fit the trace margin.
Reconstruction: The test is the gamma profile acted on by the second log
derivative minus one quarter. The central sum uses half-unit bands. -/
theorem retainedShell_polarFree_trace_constants :
    (∑ j ∈ Finset.range 26,
      let x := (j : ℚ) / 2
      let y := x + 1 / 2
      let q := y ^ 2 + 1 / 4
      (15 - x) ^ 2 * (33 / 20) ^ (2 * (j + 1)) / (1 + x ^ 2 / 64) ^ 36 *
        (q ^ 2 + 2 * (7 * q + 2 * y) ^ 2 + (853 / 16 * q + 28 * y + 2) ^ 2)) <
      (65000 : ℚ) ^ 2 ∧
    (4 : ℚ) * (501 / 1000) * 65000 / 10 ^ 6 < 131 / 1000 ∧
    (∑ n ∈ Finset.range 5,
      let j := n + 12
      let x : ℚ := (max 12 (j - 1) : ℕ)
      let y := (j : ℚ) + 1
      8 * (1 + ((j : ℚ) + 2) ^ 2) * (1225 / 16 * (y ^ 2 + 1 / 4) + 33 * y + 2) /
        (1 + x ^ 2 / 64) ^ 18) < (34 / 1000 : ℚ) ∧
    (5120 : ℚ) * (1 / 5) ^ 18 * (16 ^ 4 + 16 ^ 5 / 19) < 1 / 1000 ∧
    (8 : ℚ) * (16 / 65) ^ 18 * (14 ^ 4 + 14 ^ 5 / 19) < 1 / 1000 ∧
    (2 : ℚ) * (17 / 100 + 1 / 1000) < 2 / 5 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · norm_num [Finset.sum_range_succ]
  · norm_num
  · norm_num [Finset.sum_range_succ, max_def]
  · norm_num
  · norm_num
  · norm_num

end RiemannMasullo.Isolated
