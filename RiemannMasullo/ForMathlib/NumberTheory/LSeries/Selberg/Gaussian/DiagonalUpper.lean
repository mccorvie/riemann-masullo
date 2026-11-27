module

public import RiemannMasullo.ForMathlib.NumberTheory.LSeries.Selberg.Definitions

public section

namespace RiemannMasullo.Selberg

/-- Card 29. For bounded coefficients and 0 < q ≤ 1/2, the diagonal is at most `gaussC * energy N
b 1 / (q * scale N) + 2 N⁴`.
One-sided version of Titchmarsh (10.11.1), (10.15.1), pp. 271, 274. -/
theorem diagonal_upper (N : ℕ) (hN : 2 ≤ N) (b : ℕ → ℝ) (hb : bd N b)
    (q : ℝ) (hq : 0 < q) (hq' : q ≤ 1/2) :
    diag N b q ≤ gaussC * energy N b 1 / (q * scale N) + 2*(N : ℝ)^4 := by
  sorry

end RiemannMasullo.Selberg
