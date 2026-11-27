module

public import RiemannMasullo.ForMathlib.NumberTheory.LSeries.Selberg.Definitions

public section

open MeasureTheory

namespace RiemannMasullo.Selberg

/-- Card 36. The unweighted squared norm integral of the tapered dual is bounded by a constant
times N⁵⁰ for N ≥ 2.
Titchmarsh, Lemma 10.18, pp. 276–277. -/
theorem dual_total : ∃ C > (0 : ℝ), ∀ N : ℕ, 2 ≤ N →
    (∫ y : ℝ, ‖dual N (beta N) y‖^2) ≤ C*(N : ℝ)^50 := by
  sorry

end RiemannMasullo.Selberg
