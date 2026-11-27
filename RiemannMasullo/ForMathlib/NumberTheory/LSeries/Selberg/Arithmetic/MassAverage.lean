module

public import RiemannMasullo.ForMathlib.NumberTheory.LSeries.Selberg.Definitions

public section

namespace RiemannMasullo.Selberg

/-- Card 13. The reciprocal-weighted sum of the sixth powers of the Euler products through U is
bounded by a constant times 1 + log U.
Titchmarsh, §10.14, pp. 273–274, divisor interchange. -/
theorem mass_average : ∃ C > (0 : ℝ), ∀ U : ℕ, 1 ≤ U →
    (∑ r ∈ D U, (smoothMass r)^6 / r) ≤ C * (1+Real.log U) := by
  sorry

end RiemannMasullo.Selberg
