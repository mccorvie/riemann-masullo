module

public import RiemannMasullo.ForMathlib.NumberTheory.LSeries.Selberg.Definitions

public section

open MeasureTheory

namespace RiemannMasullo.Selberg

/-- Card 39. Integrating the Fourier transform of an integrable function over [t,t+h] equals the
transform at t of the function multiplied by the length-h window multiplier.
Titchmarsh, §10.10, (10.10.1), p. 269, short-window multiplier. -/
theorem window_transform (f : ℝ → ℂ) (hf : Integrable f) (h t : ℝ) (hh : 0 ≤ h) :
    (∫ u in t..t+h, ft f u) = ft (fun y ↦ f y * mult h y) t := by
  sorry

end RiemannMasullo.Selberg
