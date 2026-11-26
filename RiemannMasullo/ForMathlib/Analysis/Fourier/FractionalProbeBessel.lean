module

public import RiemannMasullo.ForMathlib.Analysis.Fourier.FractionalModel
import Mathlib.Analysis.Fourier.Inversion

/-! # Exact Bessel normalization of fractional Fourier evaluation probes -/

@[expose] public noncomputable section
open MeasureTheory FourierTransform
open scoped FourierTransform InnerProductSpace
namespace RiemannMasullo

/-- The model evaluation kernel is the normalized Bessel kernel divided by its
Green-pairing constant. This fixes the diagonal normalization as well as every off-diagonal. -/
theorem fractionalProbe_gram_bessel {θ : ℝ} (hθ : 1 / 2 < θ) (s t : ℝ) :
    ⟪fractionalProbe θ hθ s, fractionalProbe θ hθ t⟫_ℂ =
      ((normalizedBesselKernel θ (s - t) /
        (2 * Real.sqrt Real.pi * Real.Gamma θ / Real.Gamma (θ - 1 / 2)) : ℝ) : ℂ) := by
  let C := 2 * Real.sqrt Real.pi * Real.Gamma θ / Real.Gamma (θ - 1 / 2)
  let g : ℝ → ℂ := fun x ↦ (normalizedBesselKernel θ x : ℂ)
  have hC : 0 < C := by
    dsimp [C]
    exact div_pos (mul_pos (mul_pos (by norm_num) (Real.sqrt_pos.mpr Real.pi_pos))
      (Real.Gamma_pos_of_pos (by linarith))) (Real.Gamma_pos_of_pos (by linarith))
  have hg : Continuous g := Complex.continuous_ofReal.comp (continuous_normalizedBesselKernel hθ)
  have hgi : Integrable g := (integrable_normalizedBesselKernel hθ).ofReal
  have hF : Integrable (𝓕 g) := by
    apply ((integrable_reciprocal_fractionalSobolevWeight hθ).ofReal.const_mul (C : ℂ)).congr
    exact .of_forall fun ξ ↦ by
      rw [show 𝓕 g ξ = _ from fourier_normalizedBesselKernel hθ ξ, Complex.ofReal_mul]
      rfl
  have hInv := congrFun (hg.fourierInv_fourier_eq hgi hF) (s - t)
  rw [Real.fourierInv_eq] at hInv
  have he : (∫ ξ : ℝ, (Real.fourierChar (inner ℝ ξ (s - t)) : ℂ) • 𝓕 g ξ) =
      (C : ℂ) * ⟪fractionalProbe θ hθ s, fractionalProbe θ hθ t⟫_ℂ := by
    rw [fractionalProbe_gram hθ, ← integral_const_mul]
    apply integral_congr_ae
    exact .of_forall fun ξ ↦ by
      dsimp only
      rw [show 𝓕 g ξ = _ from fourier_normalizedBesselKernel hθ ξ]
      have hr : inner ℝ ξ (s - t) = ξ * (s - t) := by simp [RCLike.inner_apply, mul_comm]
      rw [hr, Complex.ofReal_mul, smul_eq_mul]
      change (Real.fourierChar (ξ * (s - t)) : ℂ) *
        ((C : ℂ) * (((1 + (2 * Real.pi * ξ) ^ 2) ^ (-θ) : ℝ) : ℂ)) = _
      ring
  change (∫ ξ : ℝ, (Real.fourierChar (inner ℝ ξ (s - t)) : ℂ) • 𝓕 g ξ) = g (s - t) at hInv
  rw [he] at hInv
  change _ = ((normalizedBesselKernel θ (s - t) / C : ℝ) : ℂ)
  rw [Complex.ofReal_div, eq_div_iff (Complex.ofReal_ne_zero.mpr hC.ne'), mul_comm]
  exact hInv

/-- The squared evaluation norm is the reciprocal Bessel Green constant. -/
theorem fractionalProbe_norm_sq {θ : ℝ} (hθ : 1 / 2 < θ) (t : ℝ) :
    ‖fractionalProbe θ hθ t‖ ^ 2 =
      (2 * Real.sqrt Real.pi * Real.Gamma θ / Real.Gamma (θ - 1 / 2))⁻¹ := by
  have he := congrArg Complex.re (fractionalProbe_gram_bessel hθ t t)
  rw [sub_self, normalizedBesselKernel_zero hθ, one_div, Complex.ofReal_re] at he
  exact (inner_self_eq_norm_sq (𝕜 := ℂ) _).symm.trans he

end RiemannMasullo
