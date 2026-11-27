module

public import RiemannMasullo.ForMathlib.NumberTheory.LSeries.Selberg.Definitions

public section

namespace RiemannMasullo.Selberg

/-- Card 3. Every positive integer factors uniquely into a part supported on the primes dividing r
and a part coprime to r, for r > 0.
Titchmarsh, §10.11, p. 271, supported and coprime parts. -/
theorem smooth_split (r n : ℕ) (hr : 0 < r) (hn : 0 < n) :
    ∃! de : ℕ × ℕ, smooth r de.1 ∧ Nat.Coprime r de.2 ∧ de.1*de.2=n := by
  sorry

end RiemannMasullo.Selberg
