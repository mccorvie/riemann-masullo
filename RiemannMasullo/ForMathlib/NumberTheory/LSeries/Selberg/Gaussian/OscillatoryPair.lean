module

public import RiemannMasullo.ForMathlib.NumberTheory.LSeries.Selberg.Definitions

public section

namespace RiemannMasullo.Selberg

/-- Card 30. For positive damping P, nonzero phase coefficient Q, and q ≥ 0, the weighted Gaussian
pair integral has norm at most 2 exp(−P)/|Q|.
Titchmarsh, §10.16, p. 274, first unnumbered display. -/
theorem oscillatory_pair (P Q q : ℝ) (hP : 0 < P) (hQ : Q ≠ 0) (hq : 0 ≤ q) :
    ‖pairInt P Q q‖ ≤ 2*Real.exp (-P)/|Q| := by
  sorry

end RiemannMasullo.Selberg
