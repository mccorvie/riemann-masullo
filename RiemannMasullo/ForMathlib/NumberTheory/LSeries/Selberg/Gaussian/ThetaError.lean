module

public import RiemannMasullo.ForMathlib.NumberTheory.LSeries.Selberg.Definitions

public section

namespace RiemannMasullo.Selberg

/-- Card 23. For v > 0, the Gaussian integral approximation √π/(2v) exceeds the positive mesh sum
by an amount between zero and min(1, √π/(2v)).
Titchmarsh, §10.11, pp. 270–271, elementary alternative to harmonic expansion. -/
theorem theta_error (v : ℝ) (hv : 0 < v) :
    0 ≤ gaussC/v - theta v ∧ gaussC/v - theta v ≤ min 1 (gaussC/v) := by
  sorry

end RiemannMasullo.Selberg
