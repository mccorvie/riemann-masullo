module

public import RiemannMasullo.ForMathlib.NumberTheory.LSeries.Selberg.Definitions

public section

namespace RiemannMasullo.Selberg

/-- Card 22. For coefficients bounded by one and N ≥ 2, the dual is continuous and its norm is
bounded by a constant times N⁵³ exp(−|y|/2).
Titchmarsh, §§10.10, 10.18, pp. 269, 276–277, polynomial tail envelope. -/
theorem dual_envelope : ∃ C > (0 : ℝ), ∀ N : ℕ, 2 ≤ N → ∀ b : ℕ → ℝ, bd N b →
    Continuous (dual N b) ∧ ∀ y : ℝ, ‖dual N b y‖ ≤ C*(N : ℝ)^53*Real.exp (-|y|/2) := by
  sorry

end RiemannMasullo.Selberg
