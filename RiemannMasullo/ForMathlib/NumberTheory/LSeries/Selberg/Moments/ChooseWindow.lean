module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic

public section

namespace RiemannMasullo.Selberg

/-- Card 45. For any a, ε > 0 and any prescribed threshold, some integer N above the threshold and
at least two gives 0 < 1/(a log N) ≤ 1/2 and 1/(a log N) < ε.
Titchmarsh, §§10.15, 10.22, pp. 274, 279. -/
theorem choose_window (a ε : ℝ) (ha : 0 < a) (he : 0 < ε) (N₀ : ℕ) :
    ∃ N ≥ max 2 N₀,
      let h := (a*Real.log N)⁻¹
      0 < h ∧ h ≤ 1/2 ∧ h < ε := by
  sorry

end RiemannMasullo.Selberg
