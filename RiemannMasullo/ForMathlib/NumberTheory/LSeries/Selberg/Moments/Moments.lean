module

public import RiemannMasullo.ForMathlib.NumberTheory.LSeries.Selberg.Definitions

public section

open MeasureTheory

namespace RiemannMasullo.Selberg

/-- Card 46. For arbitrarily short windows, a single normalized mollifier has positive bulk
mass. Its squared bulk mass bounds both scaled window second moments with a uniform positive
constant in the absolute-window bound.
Titchmarsh, §10.22, pp. 278–279, in the existing Lean normalization. -/
theorem moments : ∃ c > (0 : ℝ), ∀ ε > (0 : ℝ), ∃ (T N : ℕ) (b : ℕ → ℝ) (h : ℝ),
    1 ≤ T ∧ 1 ≤ N ∧ b 1 = 1 ∧ (∀ n ∈ Finset.Icc 1 N, |b n| ≤ 1) ∧
    0 < h ∧ h ≤ 1 ∧ h < ε ∧
    let w := spectralLineJet_selbergWeight T N b
    let P := h * ∫ u in h..(T : ℝ), |w u * hardyZ u|
    0 < P ∧ 4*T*second T (win (fun u ↦ w u*hardyZ u) h) ≤ P^2 ∧
      c*T*second T (win (fun u ↦ |w u*hardyZ u|) h) ≤ P^2 := by
  sorry

end RiemannMasullo.Selberg
