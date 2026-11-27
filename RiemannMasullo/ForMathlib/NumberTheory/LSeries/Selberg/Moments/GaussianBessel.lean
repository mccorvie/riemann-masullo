module

public import RiemannMasullo.ForMathlib.NumberTheory.LSeries.Selberg.Definitions

public section

open MeasureTheory

namespace RiemannMasullo.Selberg

/-- Card 37. For an integrable complex function with integrable squared norm, the Fourier energy
with Gaussian weight exp(−(t/U)²) is at most 2π times its squared norm integral for U > 0.
Elementary form of Plancherel used in Titchmarsh (10.10.1), p. 269. -/
theorem gaussian_bessel (f : ℝ → ℂ) (hf : Integrable f) (hf₂ : Integrable (fun y ↦ ‖f y‖^2))
    (U : ℝ) (hU : 0 < U) :
    (∫ t : ℝ, Real.exp (-(t/U)^2)*‖ft f t‖^2) ≤ 2*Real.pi * ∫ y : ℝ, ‖f y‖^2 := by
  sorry

end RiemannMasullo.Selberg
