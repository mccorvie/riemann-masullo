module

public import RiemannMasullo.ForMathlib.NumberTheory.LSeries.Selberg.Definitions

public section

namespace RiemannMasullo.Selberg

/-- Card 35. The squared norm integral of the tapered dual with weight exp(−q|y|) is bounded by a
constant times N⁵⁰/(q log N) for 0 < q ≤ 1/2.
Titchmarsh, §§10.10, 10.17, pp. 269–270, 275–276. -/
theorem dual_weighted : ∃ C > (0 : ℝ), ∀ N : ℕ, 2 ≤ N → ∀ q : ℝ, 0 < q → q ≤ 1/2 →
    dualMass N q ≤ C*(N : ℝ)^50/(q*Real.log N) := by
  sorry

end RiemannMasullo.Selberg
