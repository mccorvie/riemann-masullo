module

public import RiemannMasullo.ForMathlib.NumberTheory.LSeries.Selberg.Definitions

public section

namespace RiemannMasullo.Selberg

/-- Card 14. For N ≥ 2 the tapered energy at power one is bounded above by a constant times 1 /
log N.
Titchmarsh, Lemma 10.14, pp. 273–274, S(0). -/
theorem energy_one : ∃ C > (0 : ℝ), ∀ N : ℕ, 2 ≤ N →
    energy N (beta N) 1 ≤ C / Real.log N := by
  sorry

end RiemannMasullo.Selberg
