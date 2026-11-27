module

public import RiemannMasullo.ForMathlib.NumberTheory.LSeries.Selberg.Definitions

public section

open MeasureTheory

namespace RiemannMasullo.Selberg

/-- Card 40. For h > 0 the squared norm of the window multiplier at y is at most 8e times the
integral of q exp(−q|y|) from zero to h.
Replacement for the two frequency ranges in Titchmarsh (10.10.1), pp. 269, 275–276. -/
theorem mult_laplace (h y : ℝ) (hh : 0 < h) :
    ‖mult h y‖^2 ≤ 8*Real.exp 1 * ∫ q in (0 : ℝ)..h, q*Real.exp (-q*|y|) := by
  sorry

end RiemannMasullo.Selberg
