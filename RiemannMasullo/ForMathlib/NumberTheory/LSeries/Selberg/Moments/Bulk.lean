module

public import RiemannMasullo.ForMathlib.NumberTheory.LSeries.Selberg.Definitions

public section

open MeasureTheory

namespace RiemannMasullo.Selberg

/-- Card 44. For all sufficiently large N and every 0 < h ≤ 1/2, the absolute signal integral from
h to N¹⁰⁰ is bounded below by a positive constant times N⁷⁵.
Titchmarsh, Lemmas 10.20–10.21, pp. 277–278. -/
theorem bulk : ∃ D₀ > (0 : ℝ), ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ h : ℝ, 0 < h → h ≤ 1/2 →
    D₀ * (N : ℝ)^75 ≤ ∫ u in h..(H N : ℝ), |signal N u| := by
  sorry

end RiemannMasullo.Selberg
