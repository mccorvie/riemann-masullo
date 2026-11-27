module

public import RiemannMasullo.ForMathlib.NumberTheory.LSeries.Selberg.Definitions

public section

namespace RiemannMasullo.Selberg

/-- Card 10. For p > 0 the sum of the Jordan totient over the divisors of a positive integer n is
nᵖ, and its value at n lies between zero and nᵖ.
Titchmarsh, §10.11, p. 271, generalized totients. -/
theorem jordan_sum (p : ℝ) (hp : 0 < p) (n : ℕ) (hn : 0 < n) :
    (∑ r ∈ n.divisors, jordan p r) = (n : ℝ)^p ∧
      0 ≤ jordan p n ∧ jordan p n ≤ (n : ℝ)^p := by
  sorry

end RiemannMasullo.Selberg
