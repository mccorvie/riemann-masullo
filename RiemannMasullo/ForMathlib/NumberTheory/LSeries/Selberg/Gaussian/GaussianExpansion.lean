module

public import RiemannMasullo.ForMathlib.NumberTheory.LSeries.Selberg.Definitions

public section

open MeasureTheory Set

namespace RiemannMasullo.Selberg

/-- Card 26. For q ≥ 0 and N ≥ 2, the integrand defining J is integrable on (1, ∞), and J expands
into the coefficient-weighted real parts of the Gaussian pair series.
Titchmarsh, §10.11, p. 270, expansion of J. -/
theorem gaussian_expansion (N : ℕ) (hN : 2 ≤ N) (b : ℕ → ℝ) (q : ℝ) (hq : 0 ≤ q) :
    IntegrableOn (fun x : ℝ ↦ ‖g N b x‖^2*x^(-q)) (Ioi 1) ∧
    J N b q = fourSum N (fun k l m v ↦ coef b k l m v *
      (∑' ij : ℕ × ℕ, pair N k l m v q ij).re) := by
  sorry

end RiemannMasullo.Selberg
