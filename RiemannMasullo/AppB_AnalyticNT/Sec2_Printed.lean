module

public import RiemannMasullo.AppB_AnalyticNT.Sec2

/-!
# Appendix B.2: statements that are false as printed

The printed claim is kept as a proposition with a separate refutation statement.
Nothing imports this file.
-/

@[expose] public noncomputable section

namespace RiemannMasullo

/-- Paper: Theorem B.2.2.4(2), p. 602. As printed: for every holomorphic Schwartz
function on a left half-plane, every positive shift of the boundary to the left, and every
derivative order, the normalized Cauchy integral on the shifted line gives that derivative
to its left and zero to its right. These are (B.2.2.6) and (B.2.2.7).
The absolute convergence assertion is proved in
`cauchyKernel_verticalIntegrable_on_leftHalfPlane`. See ERRATA F14. -/
def Printed.asymptoticCauchy_leftHalfPlane : Prop :=
  ∀ (b : ℝ) (Φ : ℂ → ℂ), SchwartzOnLeftHalfPlane Φ b →
    ∀ ε > (0 : ℝ), ∀ (N : ℕ) (z : ℂ),
      let integral := (Nat.factorial N : ℂ) / (2 * (Real.pi : ℂ) * Complex.I) *
        verticalLineIntegral (fun s ↦ Φ s / (s - z) ^ (N + 1)) (b - ε)
      (z.re < b - ε → integral = iteratedDeriv N Φ z) ∧
        (b - ε < z.re → integral = 0)

/-- Paper: Theorem B.2.2.4(2), p. 602. On `t > 0` set
`g(t) = exp(-t log t - t^(-1/2))` and let `Φ(s) = ∫₀^∞ g(t) exp(-s t) dt`.
This transform is entire. For large positive or negative imaginary part, rotate the
integration ray to the opposite imaginary half-axis to obtain rapid decay uniformly
in the real part. Take `b = ε = 2` and `N = 0`. On the imaginary axis, Fourier
inversion gives zero for the Cauchy integral at `z = -1`, where `Φ(-1) > 0`, and
gives `-Φ(1) ≠ 0` at `z = 1`. -/
theorem Printed.asymptoticCauchy_leftHalfPlane_false :
    ¬ Printed.asymptoticCauchy_leftHalfPlane := by
  sorry

end RiemannMasullo
