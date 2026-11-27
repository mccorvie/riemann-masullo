module

public import RiemannMasullo.ForMathlib.NumberTheory.LSeries.Selberg.Definitions

public section

namespace RiemannMasullo.Selberg

/-- Card 20. For N ≥ 2 the tapered Hardy signal equals the Fourier transform of its dual
multiplied by 2π^(1/4).
Titchmarsh, §10.10, p. 269, finite mollifier inserted in the transform. -/
theorem dual_transform (N : ℕ) (hN : 2 ≤ N) (t : ℝ) :
    (signal N t : ℂ) = ((2*Real.pi ^ (1/4 : ℝ) : ℝ) : ℂ) * ft (dual N (beta N)) t := by
  sorry

end RiemannMasullo.Selberg
