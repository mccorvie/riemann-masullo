module

public import RiemannMasullo.ForMathlib.NumberTheory.LSeries.Selberg.Definitions

public section

namespace RiemannMasullo.Selberg

/-- Card 11. At each positive power the four-index energy is the sum of the squared divisor rows
through N², weighted by the Jordan totient.
Titchmarsh, §10.11, p. 271, square of the row. -/
theorem energy_rows (N : ℕ) (b : ℕ → ℝ) (p : ℝ) (hp : 0 < p) :
    energy N b p = ∑ r ∈ D (N*N), jordan p r * (row N b p r)^2 := by
  sorry

end RiemannMasullo.Selberg
