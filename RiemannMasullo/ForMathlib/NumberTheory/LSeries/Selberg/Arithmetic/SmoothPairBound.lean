module

public import RiemannMasullo.ForMathlib.NumberTheory.LSeries.Selberg.Definitions

public section

open Classical

namespace RiemannMasullo.Selberg

/-- Card 7. The absolute coefficient pairs supported on primes of r whose product is divisible by
r have reciprocal-weighted sum at most `smoothMass r / r`.
Titchmarsh, Lemma 10.13, p. 273. -/
theorem smooth_pair_bound (r N : ℕ) (hr : 0 < r) :
    (∑ d ∈ (D N).filter (smooth r), ∑ e ∈ (D N).filter (fun e ↦ smooth r e ∧ r ∣ d*e),
      |alpha d * alpha e| / ((d : ℝ)*e)) ≤ smoothMass r / r := by
  sorry

end RiemannMasullo.Selberg
