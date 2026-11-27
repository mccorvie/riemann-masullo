module

public import RiemannMasullo.ForMathlib.NumberTheory.LSeries.Selberg.Definitions

public section

open Classical

namespace RiemannMasullo.Selberg

/-- Card 8. At power one the tapered row factors into a sum over pairs of r-supported divisors.
Each term contains two coprime logarithmic sums and the denominator (log N)².
Titchmarsh, §10.11, p. 271, last display before Lemma 10.12. -/
theorem row_factor (r N : ℕ) (hr : 0 < r) (hN : 2 ≤ N) :
    row N (beta N) 1 r =
      (∑ d ∈ (D N).filter (smooth r), ∑ e ∈ (D N).filter (fun e ↦ smooth r e ∧ r ∣ d*e),
        alpha d * alpha e / ((d : ℝ)*e) * logSum r ((N : ℝ)/d) * logSum r ((N : ℝ)/e)) /
        (Real.log N)^2 := by
  sorry

end RiemannMasullo.Selberg
