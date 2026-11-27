module

public import RiemannMasullo.ForMathlib.NumberTheory.LSeries.Selberg.Definitions

public section

namespace RiemannMasullo.Selberg

/-- Card 6. Restricting the logarithmic sum through Y to indices coprime to r gives an absolute
bound of order `smoothMass r * √(1 + log Y)`, uniformly in r and Y.
Replacement for Titchmarsh Lemma 10.12, (10.12.1), pp. 271–272. -/
theorem coprime_logSum : ∃ C > (0 : ℝ), ∀ (r : ℕ) (Y : ℝ), 0 < r → 1 ≤ Y →
    |logSum r Y| ≤ C * smoothMass r * Real.sqrt (1 + Real.log Y) := by
  sorry

end RiemannMasullo.Selberg
