module

public import RiemannMasullo.ForMathlib.NumberTheory.LSeries.Selberg.Definitions

public section

open MeasureTheory

namespace RiemannMasullo.Selberg

/-- Card 41. For 0 < h ≤ 1/2 the squared norm integral of the tapered dual times the window
multiplier is bounded by a constant times h N⁵⁰/log N.
Replacement integral for the end of Titchmarsh Lemma 10.17, pp. 275–276. -/
theorem dual_window_mass : ∃ C > (0 : ℝ), ∀ N : ℕ, 2 ≤ N → ∀ h : ℝ, 0 < h → h ≤ 1/2 →
    (∫ y : ℝ, ‖dual N (beta N) y * mult h y‖^2) ≤ C*h*(N : ℝ)^50/Real.log N := by
  sorry

end RiemannMasullo.Selberg
