module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Two radial cutoffs do not share an orbital density

Step II on pp. 516–517 describes an upper cutoff. Definition 9.3.3.1 instead cuts
both a radius and its inverse. On p. 514 the section that should compare them is
only a heading. For a nonnegative test supported in `(1, √(8/7))`, the upper-only
density `r^{3/2}/(r^2-1)` strictly exceeds eight times `r^{-1/2}`. That is the room
in which an inversion-symmetric correction, bounded through `Si(u) ≤ u`, stays
strictly below the upper-only term.
-/

@[expose] public section

open Real

namespace RiemannMasullo

/-- The upper-only orbital density in the radial coordinate, before dividing by `r`. -/
noncomputable def upperOnlyOrbitalDensity (r : ℝ) : ℝ :=
  r ^ (3 / 2 : ℝ) / (r ^ 2 - 1)

/-- Eight copies of the comparison weight `r^{-1/2}` used to bound an
inversion-symmetric correction. -/
noncomputable def eightInverseSqrt (r : ℝ) : ℝ :=
  8 * r ^ (-(1 / 2 : ℝ))

theorem eightInverseSqrt_lt_upperOnlyOrbitalDensity {r : ℝ}
    (hr1 : 1 < r) (hr : r ^ 2 < 8 / 7) :
    eightInverseSqrt r < upperOnlyOrbitalDensity r := by
  have hr0 : 0 < r := lt_trans zero_lt_one hr1
  have hden : 0 < r ^ 2 - 1 := by nlinarith [hr1]
  have hneg : 0 < r ^ (-(1 / 2 : ℝ)) := Real.rpow_pos_of_pos hr0 _
  have h8 : 8 * (r ^ 2 - 1) < r ^ 2 := by nlinarith [hr]
  have hstep := mul_lt_mul_of_pos_right h8 hneg
  have hpow : r ^ 2 * r ^ (-(1 / 2 : ℝ)) = r ^ (3 / 2 : ℝ) := by
    rw [show (r ^ 2 : ℝ) = r ^ (2 : ℝ) by norm_num, ← Real.rpow_add hr0]
    norm_num
  have hleft : 8 * (r ^ 2 - 1) * r ^ (-(1 / 2 : ℝ)) =
      8 * r ^ (-(1 / 2 : ℝ)) * (r ^ 2 - 1) := by ring
  rw [hleft, hpow] at hstep
  unfold eightInverseSqrt upperOnlyOrbitalDensity
  rwa [lt_div_iff₀ hden]

end RiemannMasullo
