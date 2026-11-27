module

public import RiemannMasullo.ForMathlib.NumberTheory.LSeries.Selberg.Definitions

public section

open Classical

namespace RiemannMasullo.Selberg

/-- Card 5. For r and n positive, restricting the half-Möbius coefficients to integers coprime to
r is Dirichlet convolution with the r-supported positive half-zeta coefficients.
Replacement for Euler factors in Titchmarsh (10.12.2), p. 272. -/
theorem remove_primes (r n : ℕ) (hr : 0 < r) (hn : 0 < n) :
    (if Nat.Coprime r n then alpha n else 0) =
      ∑ d ∈ n.divisors.filter (smooth r), posHalf d * alpha (n/d) := by
  sorry

end RiemannMasullo.Selberg
