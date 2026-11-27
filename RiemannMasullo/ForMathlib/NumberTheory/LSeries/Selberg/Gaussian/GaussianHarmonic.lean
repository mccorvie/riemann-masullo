module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic

public section

namespace RiemannMasullo.Selberg

/-- Card 32. The Gaussian-damped harmonic series with its logarithmic weight converges and is
bounded by a constant times N¹⁴ for N ≥ 2.
Coarse specialization of Titchmarsh §10.16, p. 275, before (10.16.1). -/
theorem gaussian_harmonic : ∃ C > (0 : ℝ), ∀ N : ℕ, 2 ≤ N →
    let term := fun i : ℕ ↦ let u : ℝ := (i : ℝ)+1
      Real.exp (-u^2/(2*(N : ℝ)^102)) * (1+Real.log (u*N^2))/u
    Summable term ∧ ∑' i, term i ≤ C*(N : ℝ)^14 := by
  sorry

end RiemannMasullo.Selberg
