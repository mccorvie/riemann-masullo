module

public import RiemannMasullo.ForMathlib.NumberTheory.LSeries.Selberg.Definitions

public section

namespace RiemannMasullo.Selberg

/-- Card 21. Reflection in y conjugates the dual function. At y the dual decomposes into the
rotated Gaussian sum at exp(y) and its explicit correction involving `constTerm`.
Titchmarsh, §§10.10–10.11, pp. 269–270, positive half of f. -/
theorem dual_formula (N : ℕ) (hN : 2 ≤ N) (b : ℕ → ℝ) (y : ℝ) :
    dual N b (-y) = star (dual N b y) ∧
    dual N b y = ((Real.exp (y/2) : ℝ) : ℂ)*osc (angle N/2) *
      (g N b (Real.exp y) - osc (-angle N)*(constTerm N b : ℂ)/(2*(Real.exp y : ℂ))) := by
  sorry

end RiemannMasullo.Selberg
