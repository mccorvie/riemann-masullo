module

public import RiemannMasullo.ForMathlib.NumberTheory.LSeries.Selberg.Definitions

public section

namespace RiemannMasullo.Selberg

/-- Card 33. For every sequence bounded by one, the total contribution to J from unequal
frequencies has absolute value at most a constant times N²², uniformly for q ≥ 0.
Weaker power-saving substitute for Titchmarsh (10.16.1), pp. 274–275. -/
theorem off_diagonal : ∃ C > (0 : ℝ), ∀ N : ℕ, 2 ≤ N → ∀ b : ℕ → ℝ, bd N b →
    ∀ q : ℝ, 0 ≤ q → |J N b q - diag N b q| ≤ C*(N : ℝ)^22 := by
  sorry

end RiemannMasullo.Selberg
