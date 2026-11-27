module

public import RiemannMasullo.ForMathlib.NumberTheory.LSeries.Selberg.Definitions

public section

namespace RiemannMasullo.Selberg

/-- Card 2. The logarithmically weighted sum of the untwisted half-Möbius coefficients through Y
is bounded in absolute value by a constant times √(1 + log Y) for Y ≥ 1.
Replacement for Titchmarsh (10.12.1), pp. 271–272, θ=0. -/
theorem untwisted_logSum : ∃ C > (0 : ℝ), ∀ Y : ℝ, 1 ≤ Y →
    |logSum 1 Y| ≤ C * Real.sqrt (1 + Real.log Y) := by
  sorry

end RiemannMasullo.Selberg
