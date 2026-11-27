module

public import RiemannMasullo.ForMathlib.NumberTheory.LSeries.Selberg.Definitions

public section

namespace RiemannMasullo.Selberg

/-- Card 1. For N ≥ 2 the logarithmic taper has first coefficient one, and its coefficients
through N have absolute value at most one.
Titchmarsh, §10.9, pp. 268–269. -/
theorem taper_spec (N : ℕ) (hN : 2 ≤ N) :
    beta N 1 = 1 ∧ bd N (beta N) := by
  sorry

end RiemannMasullo.Selberg
