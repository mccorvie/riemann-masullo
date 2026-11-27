module

public import RiemannMasullo.ForMathlib.NumberTheory.LSeries.Selberg.Definitions

public section

namespace RiemannMasullo.Selberg

/-- Card 9. For r ≥ 1 and N ≥ 2, the absolute tapered row at power one is bounded by a constant
times `(smoothMass r)³ / (r log N)`.
Titchmarsh, §10.14, p. 273, inner row bound with a larger Euler product. -/
theorem row_bound : ∃ C > (0 : ℝ), ∀ N r : ℕ, 2 ≤ N → 0 < r →
    |row N (beta N) 1 r| ≤ C * (smoothMass r)^3 / (r * Real.log N) := by
  sorry

end RiemannMasullo.Selberg
