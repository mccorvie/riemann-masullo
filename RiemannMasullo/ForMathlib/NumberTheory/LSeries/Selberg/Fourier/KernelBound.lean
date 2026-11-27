module

public import RiemannMasullo.ForMathlib.NumberTheory.LSeries.Selberg.Definitions

public section

namespace RiemannMasullo.Selberg

/-- Card 16. On the strip |Im z| < π/4, the kernel decays as exp(−|Re z|/2) with a uniform factor
bounded by a constant times 1 + 1/√cos(2 Im z).
Titchmarsh, §10.10, p. 269, domination for rotation and inversion. -/
theorem kernel_bound : ∃ C > (0 : ℝ), ∀ z : ℂ, |z.im| < Real.pi/4 →
    ‖K z‖ ≤ C * (1 + (Real.sqrt (Real.cos (2*z.im)))⁻¹) * Real.exp (-|z.re|/2) := by
  sorry

end RiemannMasullo.Selberg
