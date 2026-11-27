module

public import RiemannMasullo.ForMathlib.NumberTheory.LSeries.Selberg.Definitions

public section

open MeasureTheory Set

namespace RiemannMasullo.Selberg

/-- Card 38. For an integrable complex function with integrable squared norm, its Fourier energy
on (0,U] is at most 2πe times its squared norm integral for U > 0.
Restriction of Titchmarsh §10.10 Plancherel to the Lean domain, p. 269. -/
theorem interval_bessel (f : ℝ → ℂ) (hf : Integrable f) (hf₂ : Integrable (fun y ↦ ‖f y‖^2))
    (U : ℝ) (hU : 0 < U) :
    (∫ t in Ioc (0 : ℝ) U, ‖ft f t‖^2) ≤
      2*Real.pi*Real.exp 1 * ∫ y : ℝ, ‖f y‖^2 := by
  sorry

end RiemannMasullo.Selberg
