module

public import RiemannMasullo.ForMathlib.NumberTheory.LSeries.Selberg.Definitions

public section

namespace RiemannMasullo.Selberg

/-- Card 15. On the open strip |Im z| < π/4, the corrected theta kernel is even, commutes with
conjugation, and is complex differentiable.
Titchmarsh, §10.10, p. 269, theta transformation, also §10.1 p. 254. -/
theorem kernel_symmetry {z : ℂ} (hz : |z.im| < Real.pi/4) :
    K (-z) = K z ∧ K (star z) = star (K z) ∧ DifferentiableAt ℂ K z := by
  sorry

end RiemannMasullo.Selberg
