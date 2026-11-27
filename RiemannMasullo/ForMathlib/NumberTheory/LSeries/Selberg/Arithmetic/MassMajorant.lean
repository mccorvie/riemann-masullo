module

public import RiemannMasullo.ForMathlib.NumberTheory.LSeries.Selberg.Definitions

public section

namespace RiemannMasullo.Selberg

/-- Card 12. The sixth power of the Euler product for r is bounded by a constant times the sum of
the reciprocal square roots of the divisors of r.
Titchmarsh, §10.14, p. 273, last display, with exponent six. -/
theorem mass_majorant : ∃ C > (0 : ℝ), ∀ r : ℕ, 0 < r →
    (smoothMass r)^6 ≤ C * ∑ d ∈ r.divisors, (Real.sqrt d)⁻¹ := by
  sorry

end RiemannMasullo.Selberg
