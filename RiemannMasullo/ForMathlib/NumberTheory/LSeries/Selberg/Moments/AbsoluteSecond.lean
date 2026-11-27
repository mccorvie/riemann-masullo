module

public import RiemannMasullo.ForMathlib.NumberTheory.LSeries.Selberg.Definitions

public section

namespace RiemannMasullo.Selberg

/-- Card 43. For 0 < h ≤ 1/2 the absolute window second moment on (0,N¹⁰⁰] is bounded by a
constant times h² N⁵⁰.
Titchmarsh, Lemmas 10.18–10.19, pp. 276–277. -/
theorem absolute_second : ∃ A > (0 : ℝ), ∀ N : ℕ, 2 ≤ N → ∀ h : ℝ, 0 < h → h ≤ 1/2 →
    second (H N) (win (fun t ↦ |signal N t|) h) ≤ A*h^2*(N : ℝ)^50 := by
  sorry

end RiemannMasullo.Selberg
