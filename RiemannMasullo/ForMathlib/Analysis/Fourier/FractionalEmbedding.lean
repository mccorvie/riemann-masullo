module

public import RiemannMasullo.ForMathlib.Analysis.Fourier.BesselKernel
public import RiemannMasullo.ForMathlib.Analysis.Fourier.L2Inverse
import Mathlib.MeasureTheory.Function.L2Space

/-! # The one-dimensional fractional Sobolev evaluation threshold

The reciprocal half-weight is square-integrable for `θ > 1/2`. Cauchy–Schwarz therefore
makes a Fourier transform integrable whenever its fractional Sobolev energy is finite.
-/

@[expose] public noncomputable section
open MeasureTheory Real
namespace RiemannMasullo

/-- Squaring the half-weight gives the exact fractional Sobolev energy density. -/
theorem memLp_fractionalWeight_iff_integrable {θ : ℝ} {u : ℝ → ℂ} (hu : Measurable u) :
    MemLp (fun ξ : ℝ ↦ ((1 + (2 * Real.pi * ξ) ^ 2) ^ (θ / 2) : ℝ) • u ξ) 2 ↔
      Integrable (fun ξ : ℝ ↦ (1 + (2 * Real.pi * ξ) ^ 2) ^ θ * ‖u ξ‖ ^ 2) := by
  rw [memLp_two_iff_integrable_sq_norm (by apply Measurable.aestronglyMeasurable; fun_prop)]
  apply integrable_congr
  exact .of_forall fun ξ ↦ by
    dsimp only
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos (by positivity) _), mul_pow,
      ← Real.rpow_mul_natCast (by positivity)]
    congr 2
    ring

/-- Above the point-evaluation threshold, the reciprocal half-weight belongs to `L²`. -/
theorem memLp_two_reciprocal_fractionalHalfWeight {θ : ℝ} (hθ : 1 / 2 < θ) :
    MemLp (fun ξ : ℝ ↦ (1 + (2 * Real.pi * ξ) ^ 2) ^ (-θ / 2)) 2 := by
  apply (memLp_two_iff_integrable_sq (by apply Measurable.aestronglyMeasurable; fun_prop)).mpr
  apply (integrable_reciprocal_fractionalSobolevWeight hθ).congr
  exact .of_forall fun ξ ↦ by
    dsimp only
    rw [← Real.rpow_mul_natCast (by positivity)]
    congr 1
    ring

/-- Cauchy–Schwarz makes the Fourier transform integrable above the one-dimensional
Sobolev evaluation threshold. -/
theorem integrable_of_memLp_fractionalWeight {θ : ℝ} (hθ : 1 / 2 < θ) {u : ℝ → ℂ}
    (hu : MemLp (fun ξ : ℝ ↦ ((1 + (2 * Real.pi * ξ) ^ 2) ^ (θ / 2) : ℝ) • u ξ) 2) :
    Integrable u := by
  have hi := (memLp_two_reciprocal_fractionalHalfWeight hθ).ofReal.integrable_mul hu
  apply hi.congr
  exact .of_forall fun ξ ↦ by
    dsimp
    rw [← mul_assoc, ← Complex.ofReal_mul,
      ← Real.rpow_add (by positivity), show -θ / 2 + θ / 2 = 0 by ring,
      Real.rpow_zero, Complex.ofReal_one, one_mul]


/-- Continuous fractional Sobolev functions are recovered by the inverse Fourier integral
at every point, with no separate `L¹` hypothesis in physical space. -/
theorem fractionalSobolev_eq_fourierInv {θ : ℝ} (hθ : 1 / 2 < θ)
    {f : ℝ → ℂ} (hf : Continuous f) (hf₂ : MemLp f 2)
    (hweight : MemLp (fun ξ : ℝ ↦ ((1 + (2 * Real.pi * ξ) ^ 2) ^ (θ / 2) : ℝ) •
      (FourierTransform.fourier (hf₂.toLp f) : Lp ℂ 2 (volume : Measure ℝ)) ξ) 2) :
    f = FourierTransformInv.fourierInv
      ((FourierTransform.fourier (hf₂.toLp f) : Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ) :=
  continuous_eq_fourierInv_L2 hf hf₂ (integrable_of_memLp_fractionalWeight hθ hweight)

/-- The normalized Bessel Green kernel pairs with a fractional Sobolev function by
point evaluation at zero. The constant is explicit in the unnormalized heat convention. -/
theorem normalizedBesselKernel_fourier_pairing {θ : ℝ} (hθ : 1 / 2 < θ)
    {f : ℝ → ℂ} (hf : Continuous f) (hf₂ : MemLp f 2)
    (hweight : MemLp (fun ξ : ℝ ↦ ((1 + (2 * Real.pi * ξ) ^ 2) ^ (θ / 2) : ℝ) •
      (FourierTransform.fourier (hf₂.toLp f) : Lp ℂ 2 (volume : Measure ℝ)) ξ) 2) :
    (∫ ξ : ℝ, ((1 + (2 * Real.pi * ξ) ^ 2) ^ θ : ℝ) •
      (star (FourierTransform.fourier (fun x : ℝ ↦ (normalizedBesselKernel θ x : ℂ)) ξ) *
        (FourierTransform.fourier (hf₂.toLp f) : Lp ℂ 2 (volume : Measure ℝ)) ξ)) =
      ((2 * Real.sqrt Real.pi * Real.Gamma θ / Real.Gamma (θ - 1 / 2) : ℝ) : ℂ) * f 0 := by
  let C := 2 * Real.sqrt Real.pi * Real.Gamma θ / Real.Gamma (θ - 1 / 2)
  let F : ℝ → ℂ := (FourierTransform.fourier (hf₂.toLp f) : Lp ℂ 2 (volume : Measure ℝ))
  have he (ξ : ℝ) : ((1 + (2 * Real.pi * ξ) ^ 2) ^ θ : ℝ) •
      (star (FourierTransform.fourier (fun x : ℝ ↦ (normalizedBesselKernel θ x : ℂ)) ξ) * F ξ) =
        (C : ℂ) * F ξ := by
    rw [fourier_normalizedBesselKernel hθ, Complex.star_def, Complex.conj_ofReal,
      Complex.real_smul, ← mul_assoc, ← Complex.ofReal_mul]
    congr 2
    change (1 + (2 * Real.pi * ξ) ^ 2) ^ θ *
      (C * (1 + (2 * Real.pi * ξ) ^ 2) ^ (-θ)) = C
    rw [mul_left_comm, ← Real.rpow_add (by positivity), add_neg_cancel,
      Real.rpow_zero, mul_one]
  change (∫ ξ : ℝ, ((1 + (2 * Real.pi * ξ) ^ 2) ^ θ : ℝ) •
    (star (FourierTransform.fourier (fun x : ℝ ↦ (normalizedBesselKernel θ x : ℂ)) ξ) * F ξ)) =
      (C : ℂ) * f 0
  simp_rw [he]
  rw [integral_const_mul]
  congr 1
  have hf0 := congrFun (fractionalSobolev_eq_fourierInv hθ hf hf₂ hweight) 0
  rw [Real.fourierInv_eq'] at hf0
  simpa only [inner_zero_right, mul_zero, Complex.ofReal_zero, zero_mul, Complex.exp_zero,
    one_smul] using hf0.symm

end RiemannMasullo
