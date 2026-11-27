module

public import RiemannMasullo.ForMathlib.NumberTheory.LSeries.Selberg.Definitions

public section

open MeasureTheory Set

namespace RiemannMasullo.Selberg

/-- Card 24. For 0 < q ≤ 1/2 and z > 0 the weighted theta integral differs from `gaussC/(q*z) +
z^(q-1)*errorC q` by at most two. The coefficient `errorC q` is nonpositive.
Replacement for Titchmarsh (10.11.1), pp. 270–271, x=1. -/
theorem theta_mellin_error (q z : ℝ) (hq : 0 < q) (hq' : q ≤ 1/2) (hz : 0 < z) :
    errorC q ≤ 0 ∧
    |(∫ x in Ioi (1 : ℝ), x^(-q)*theta (z*x)) -
      (gaussC/(q*z) + z^(q-1)*errorC q)| ≤ 2 := by
  sorry

end RiemannMasullo.Selberg
