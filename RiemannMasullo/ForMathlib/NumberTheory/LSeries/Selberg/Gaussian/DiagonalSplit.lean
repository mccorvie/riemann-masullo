module

public import RiemannMasullo.ForMathlib.NumberTheory.LSeries.Selberg.Definitions

public section

namespace RiemannMasullo.Selberg

/-- Card 28. The weighted Gaussian integral is its equal-frequency contribution plus the series of
pairs with unequal frequencies.
Titchmarsh, §10.11, p. 270, Σ₁+Σ₂. -/
theorem diagonal_split (N : ℕ) (hN : 2 ≤ N) (b : ℕ → ℝ) (q : ℝ) (hq : 0 ≤ q) :
    J N b q = diag N b q + fourSum N (fun k l m v ↦ coef b k l m v *
      (∑' ij : ℕ × ℕ, if freq ij.1 k l = freq ij.2 m v then 0
        else pair N k l m v q ij).re) := by
  sorry

end RiemannMasullo.Selberg
