module

public import RiemannMasullo.ForMathlib.NumberTheory.LSeries.Selberg.Definitions

public section

namespace RiemannMasullo.Selberg

/-- Card 34. For the taper and 0 < q ≤ 1/2, the weighted Gaussian integral J is bounded above by a
constant times N⁵⁰/(q log N).
Titchmarsh, (10.17.2), p. 275, needed only at x=1. -/
theorem weighted_gaussian : ∃ C > (0 : ℝ), ∀ N : ℕ, 2 ≤ N → ∀ q : ℝ,
    0 < q → q ≤ 1/2 → J N (beta N) q ≤ C*(N : ℝ)^50/(q*Real.log N) := by
  sorry

end RiemannMasullo.Selberg
