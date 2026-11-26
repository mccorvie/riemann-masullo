module

public import RiemannMasullo.ForMathlib.Analysis.Fourier.BesselGreen
public import RiemannMasullo.ForMathlib.Analysis.FunctionalSpaces.JumpResidual
public import RiemannMasullo.ForMathlib.Analysis.Calculus.MeanValueDecay

/-! # Uniform fractional cardinal residual bounds

The positive jump representation, normalized Bessel Green comparison and exact product
cancellation give a residual-energy estimate independent of interpolation-site spacing.
The order is `θ = s / 2` in the repository's squared Sobolev-weight convention.
-/

@[expose] public noncomputable section
open MeasureTheory Real
namespace RiemannMasullo

/-- A fractional cardinal residual has an energy bound independent of node spacing and
of the cardinal interpolant's own energy. The only test-function constant on the right is
its locally weighted Lipschitz bound at the selected node. -/
theorem fractional_cardinal_residual_energy_le {θ : ℝ}
    (hθ : 1 / 2 < θ) (hθ₁ : θ < 1) (S : Set ℝ) {z A : ℝ} {h : ℝ → ℝ} {b : ℝ → ℂ}
    (hc : Continuous h) (h₂ : MemLp h 2)
    (hJ : MemLp (fun p : ℝ × ℝ ↦ h p.1 - h p.2) 2
      (realJumpPairMeasure (fractionalJumpMeasure θ)))
    (hz : h z = 1) (hS : ∀ y ∈ S, h y = 0) (hA : 0 ≤ A) {B L : NNReal}
    (hB : ∀ x, ‖b x‖ ≤ B) (hb : LipschitzWith L b) (bz : b z = 0)
    (hbw : ∀ x y, ‖b x - b y‖ ≤ A * |x - y| *
      Real.exp ((|x - z| + |y - z|) / 8))
    (horth : ∀ v : ℝ → ℝ, Continuous v → MemLp v 2 →
      MemLp (fun p : ℝ × ℝ ↦ v p.1 - v p.2) 2
        (realJumpPairMeasure (fractionalJumpMeasure θ)) →
      v z = 0 → (∀ y ∈ S, v y = 0) →
      realNonlocalPairing volume (realJumpPairMeasure (fractionalJumpMeasure θ)) h v = 0) :
    nonlocalEnergy volume (realJumpPairMeasure (fractionalJumpMeasure θ))
      (fun x ↦ (h x : ℂ) * b x) ≤
      8 * θ * ((2 : ℝ) ^ (θ - 1 / 2)) ^ 2 * A ^ 2 := by
  have henv := fractional_cardinal_nonneg_and_le_bessel hθ hθ₁ S z hc h₂ hJ hz hS horth
  have he := nonlocal_cardinal_residual_energy_le (fractionalJumpMeasure θ) S
    hc h₂ hJ hS (C := (2 : ℝ) ^ (θ - 1 / 2)) (by positivity) hA
    (fun x ↦ (henv x).1) (fun x ↦ (henv x).2.trans (normalizedBesselKernel_le_exp hθ (x - z)))
    hB hb bz hbw (integrable_sq_fractionalJumpMeasure (show 0 ≤ θ by linarith) hθ₁) horth
  rw [integral_sq_fractionalJumpMeasure (show 0 ≤ θ by linarith) hθ₁] at he
  convert he using 1; ring

/-- A rapidly decreasing multiplier derivative gives the same polynomial decay in the
cardinal residual, uniformly over all interpolation configurations. The centered symbol
vanishes at the selected node by construction. -/
theorem fractional_cardinal_residual_energy_le_of_deriv_decay {θ : ℝ}
    (hθ : 1 / 2 < θ) (hθ₁ : θ < 1) (S : Set ℝ) {z D : ℝ}
    {h : ℝ → ℝ} {m : ℝ → ℂ} (hc : Continuous h) (h₂ : MemLp h 2)
    (hJ : MemLp (fun p : ℝ × ℝ ↦ h p.1 - h p.2) 2
      (realJumpPairMeasure (fractionalJumpMeasure θ)))
    (hz : h z = 1) (hS : ∀ y ∈ S, h y = 0)
    {B L : NNReal} (hB : ∀ x, ‖m x‖ ≤ B) (hL : LipschitzWith L m)
    (hm : Differentiable ℝ m) (hD : 0 ≤ D) (n : ℕ)
    (hdecay : ∀ u, ‖deriv m u‖ * (1 + |u|) ^ n ≤ D)
    (horth : ∀ v : ℝ → ℝ, Continuous v → MemLp v 2 →
      MemLp (fun p : ℝ × ℝ ↦ v p.1 - v p.2) 2
        (realJumpPairMeasure (fractionalJumpMeasure θ)) →
      v z = 0 → (∀ y ∈ S, v y = 0) →
      realNonlocalPairing volume (realJumpPairMeasure (fractionalJumpMeasure θ)) h v = 0) :
    nonlocalEnergy volume (realJumpPairMeasure (fractionalJumpMeasure θ))
      (fun x ↦ (h x : ℂ) * (m x - m z)) ≤
      8 * θ * ((2 : ℝ) ^ (θ - 1 / 2)) ^ 2 *
        (D * ((8 : ℝ) ^ n * (n.factorial : ℝ) * Real.exp (1 / 8)) / (1 + |z|) ^ n) ^ 2 := by
  have hBb : ∀ x, ‖m x - m z‖ ≤ (2 * B : NNReal) := by
    intro x
    have ht := norm_sub_le (m x) (m z)
    simp only [NNReal.coe_mul, NNReal.coe_ofNat]
    linarith [hB x, hB z]
  have hLb : LipschitzWith L (fun x ↦ m x - m z) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    simpa only [dist_eq_norm, sub_sub_sub_cancel_right] using hL.norm_sub_le x y
  apply fractional_cardinal_residual_energy_le hθ hθ₁ S hc h₂ hJ hz hS
    (by positivity) hBb hLb (sub_self _) _ horth
  intro x y
  simpa only [sub_sub_sub_cancel_right] using
    norm_sub_le_local_exp_of_deriv_decay hm hD n hdecay z x y

end RiemannMasullo
