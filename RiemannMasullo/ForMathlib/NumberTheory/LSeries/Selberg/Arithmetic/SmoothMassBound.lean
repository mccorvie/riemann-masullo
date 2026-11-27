module

public import RiemannMasullo.ForMathlib.NumberTheory.LSeries.Selberg.Definitions

public section

open Classical

namespace RiemannMasullo.Selberg

/-- Card 4. The sum of the reciprocals of the r-supported positive integers through B is bounded
by the Euler product `smoothMass r`.
Titchmarsh, §10.13, p. 273, finite geometric majorant. -/
theorem smooth_mass_bound (r B : ℕ) (hr : 0 < r) :
    (∑ d ∈ (D B).filter (smooth r), (d : ℝ)⁻¹) ≤ smoothMass r := by
  sorry

end RiemannMasullo.Selberg
