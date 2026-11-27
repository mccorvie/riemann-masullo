module

public import RiemannMasullo.ForMathlib.NumberTheory.LSeries.Selberg.Definitions

public section

namespace RiemannMasullo.Selberg

/-- Card 42. For 0 < h ≤ 1/2 the signed window second moment on (0,N¹⁰⁰] is bounded by a constant
times h N⁵⁰/log N.
Titchmarsh, (10.17.1), p. 275. -/
theorem signed_second : ∃ B > (0 : ℝ), ∀ N : ℕ, 2 ≤ N → ∀ h : ℝ, 0 < h → h ≤ 1/2 →
    second (H N) (win (signal N) h) ≤ B*h*(N : ℝ)^50/Real.log N := by
  sorry

end RiemannMasullo.Selberg
