module

public import RiemannMasullo.ForMathlib.Analysis.Fourier.FractionalPairing
public import RiemannMasullo.ForMathlib.Analysis.FunctionalSpaces.NonlocalCardinal
public import RiemannMasullo.ForMathlib.Analysis.FunctionalSpaces.JumpTranslation

/-! # Fractional Bessel Green kernels and cardinal comparison

For `1/2 < θ < 1`, the normalized heat-integral Bessel kernel belongs to the full energy
domain and represents point evaluation in the positive jump pairing. Positive-part tests
then bound every cardinal minimizer between zero and the translated single-point kernel.
-/

@[expose] public noncomputable section
open MeasureTheory FourierTransform Real
open scoped FourierTransform
namespace RiemannMasullo

private theorem fourier_toLp_eq_of_integrable {f : ℝ → ℂ} (hf : MemLp f 2)
    (hi : Integrable f) :
    ((𝓕 (hf.toLp f) : Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ) =ᵐ[volume] 𝓕 f := by
  have hi' : Integrable (hf.toLp f : ℝ → ℂ) := hi.congr hf.coeFn_toLp.symm
  have he := fourier_L2_coeFn_of_integrable (hf.toLp f) hi'
  filter_upwards [he] with ξ hξ
  rw [hξ, Real.fourier_real_eq, Real.fourier_real_eq]
  apply integral_congr_ae
  filter_upwards [hf.coeFn_toLp] with x hx
  simp only [hx]

/-- The normalized Bessel kernel belongs to its own fractional energy domain. -/
theorem memLp_fractionalWeight_normalizedBesselKernel {θ : ℝ} (hθ : 1 / 2 < θ) :
    MemLp (fun ξ : ℝ ↦ ((1 + (2 * Real.pi * ξ) ^ 2) ^ (θ / 2) : ℝ) •
      (𝓕 ((memLp_two_normalizedBesselKernel hθ).ofReal.toLp
        (fun x ↦ (normalizedBesselKernel θ x : ℂ))) : Lp ℂ 2 (volume : Measure ℝ)) ξ) 2 := by
  let C := 2 * Real.sqrt Real.pi * Real.Gamma θ / Real.Gamma (θ - 1 / 2)
  let f : ℝ → ℂ := fun x ↦ (normalizedBesselKernel θ x : ℂ)
  have hf : MemLp f 2 := (memLp_two_normalizedBesselKernel hθ).ofReal
  let F : ℝ → ℂ := (𝓕 (hf.toLp f) : Lp ℂ 2 (volume : Measure ℝ))
  have hF : Measurable F := (Lp.stronglyMeasurable (𝓕 (hf.toLp f))).measurable
  apply (memLp_fractionalWeight_iff_integrable hF).mpr
  have he := fourier_toLp_eq_of_integrable hf ((integrable_normalizedBesselKernel hθ).ofReal)
  apply ((integrable_reciprocal_fractionalSobolevWeight hθ).const_mul (C ^ 2)).congr
  filter_upwards [he] with ξ hξ
  dsimp only [F]
  rw [hξ, fourier_normalizedBesselKernel hθ, Complex.norm_real, Real.norm_eq_abs,
    sq_abs]
  change C ^ 2 * (1 + (2 * Real.pi * ξ) ^ 2) ^ (-θ) =
    (1 + (2 * Real.pi * ξ) ^ 2) ^ θ * (C * (1 + (2 * Real.pi * ξ) ^ 2) ^ (-θ)) ^ 2
  rw [mul_pow C ((1 + (2 * Real.pi * ξ) ^ 2) ^ (-θ)) 2,
    ← Real.rpow_mul_natCast (by positivity), mul_left_comm, ← Real.rpow_add (by positivity)]
  congr 2
  ring

/-- The Bessel Green kernel has square-integrable jumps against the fractional measure. -/
theorem memLp_jump_normalizedBesselKernel {θ : ℝ} (hθ : 1 / 2 < θ) (hθ₁ : θ < 1) :
    MemLp (fun p : ℝ × ℝ ↦ normalizedBesselKernel θ p.1 - normalizedBesselKernel θ p.2) 2
      (realJumpPairMeasure (fractionalJumpMeasure θ)) := by
  have hc := continuous_normalizedBesselKernel hθ
  have he := (memLp_fractionalWeight_iff_memLp_jump (show 0 ≤ θ by linarith) hθ₁
    (f := fun x ↦ (normalizedBesselKernel θ x : ℂ)) (by fun_prop)
    (memLp_two_normalizedBesselKernel hθ).ofReal).mp
      (memLp_fractionalWeight_normalizedBesselKernel hθ)
  simpa only [Complex.sub_re, Complex.ofReal_re, RCLike.re_to_complex] using he.re

/-- The normalized Bessel kernel is the Green function for the actual jump pairing,
with the explicit Fourier normalization constant. -/
theorem realNonlocalPairing_normalizedBesselKernel {θ : ℝ}
    (hθ : 1 / 2 < θ) (hθ₁ : θ < 1) {v : ℝ → ℝ} (vc : Continuous v) (hv : MemLp v 2)
    (vJ : MemLp (fun p : ℝ × ℝ ↦ v p.1 - v p.2) 2
      (realJumpPairMeasure (fractionalJumpMeasure θ))) :
    realNonlocalPairing volume (realJumpPairMeasure (fractionalJumpMeasure θ))
      (normalizedBesselKernel θ) v =
      (2 * Real.sqrt Real.pi * Real.Gamma θ / Real.Gamma (θ - 1 / 2)) * v 0 := by
  let C := 2 * Real.sqrt Real.pi * Real.Gamma θ / Real.Gamma (θ - 1 / 2)
  let V : ℝ → ℂ := (𝓕 (hv.ofReal.toLp (fun x ↦ (v x : ℂ))) : Lp ℂ 2 (volume : Measure ℝ))
  have vJc : MemLp (fun p : ℝ × ℝ ↦ (v p.1 : ℂ) - (v p.2 : ℂ)) 2
      (realJumpPairMeasure (fractionalJumpMeasure θ)) := by
    apply (vJ.ofReal (K := ℂ)).ae_eq
    exact .of_forall fun p ↦ by dsimp only; exact RCLike.ofReal_sub _ _
  have hW := (memLp_fractionalWeight_iff_memLp_jump (show 0 ≤ θ by linarith) hθ₁
    (f := fun x ↦ (v x : ℂ)) (by fun_prop) hv.ofReal).mpr vJc
  have hVi : Integrable V := integrable_of_memLp_fractionalWeight hθ hW
  have hv0 : (∫ ξ : ℝ, V ξ) = (v 0 : ℂ) := by
    have he := congrFun (fractionalSobolev_eq_fourierInv hθ
      (f := fun x ↦ (v x : ℂ)) (by fun_prop) hv.ofReal hW) 0
    rw [Real.fourierInv_eq'] at he
    simpa only [inner_zero_right, mul_zero, Complex.ofReal_zero, zero_mul,
      Complex.exp_zero, one_smul] using he.symm
  have hVr : (∫ ξ : ℝ, (V ξ).re) = v 0 := by
    have he := Complex.reCLM.integral_comp_comm hVi
    simpa only [Complex.reCLM_apply, hv0, Complex.ofReal_re] using he
  rw [realNonlocalPairing_eq_fractionalFourierPairing_re (show 0 ≤ θ by linarith) hθ₁
    (continuous_normalizedBesselKernel hθ).measurable vc.measurable
    (memLp_two_normalizedBesselKernel hθ) hv (memLp_jump_normalizedBesselKernel hθ hθ₁) vJ]
  have hK := fourier_toLp_eq_of_integrable (memLp_two_normalizedBesselKernel hθ).ofReal
    (integrable_normalizedBesselKernel hθ).ofReal
  calc
    _ = ∫ ξ : ℝ, C * (V ξ).re := by
      apply integral_congr_ae
      filter_upwards [hK] with ξ hξ
      erw [hξ, fourier_normalizedBesselKernel hθ]
      rw [Complex.star_def,
        Complex.conj_ofReal, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
        zero_mul, sub_zero]
      change (1 + (2 * Real.pi * ξ) ^ 2) ^ θ *
        ((C * (1 + (2 * Real.pi * ξ) ^ 2) ^ (-θ)) * (V ξ).re) = C * (V ξ).re
      rw [← mul_assoc, mul_left_comm, ← Real.rpow_add (by positivity),
        add_neg_cancel, Real.rpow_zero, mul_one]
    _ = _ := by rw [integral_const_mul, hVr]

/-- The Green identity holds at every real center, with the same normalization. -/
theorem realNonlocalPairing_translatedBesselKernel {θ : ℝ}
    (hθ : 1 / 2 < θ) (hθ₁ : θ < 1) (z : ℝ) {v : ℝ → ℝ}
    (vc : Continuous v) (hv : MemLp v 2)
    (vJ : MemLp (fun p : ℝ × ℝ ↦ v p.1 - v p.2) 2
      (realJumpPairMeasure (fractionalJumpMeasure θ))) :
    realNonlocalPairing volume (realJumpPairMeasure (fractionalJumpMeasure θ))
      (fun x ↦ normalizedBesselKernel θ (x - z)) v =
      (2 * Real.sqrt Real.pi * Real.Gamma θ / Real.Gamma (θ - 1 / 2)) * v z := by
  rw [realNonlocalPairing_sub_translation]
  have hv' := hv.comp_measurePreserving (measurePreserving_add_right (volume : Measure ℝ) z)
  have vJ' := memLp_jump_translation (fractionalJumpMeasure θ) vJ z
  simpa only [zero_add] using realNonlocalPairing_normalizedBesselKernel hθ hθ₁
    (v := fun x ↦ v (x + z)) (by fun_prop) hv' vJ'

/-- Every real fractional Sobolev cardinal minimizer lies between zero and the normalized
single-point Bessel kernel. There is no lower bound on spacing between interpolation sites. -/
theorem fractional_cardinal_nonneg_and_le_bessel {θ : ℝ}
    (hθ : 1 / 2 < θ) (hθ₁ : θ < 1) (S : Set ℝ) (z : ℝ) {h : ℝ → ℝ}
    (hc : Continuous h) (hh : MemLp h 2)
    (hJ : MemLp (fun p : ℝ × ℝ ↦ h p.1 - h p.2) 2
      (realJumpPairMeasure (fractionalJumpMeasure θ)))
    (hz : h z = 1) (hS : ∀ y ∈ S, h y = 0)
    (horth : ∀ v : ℝ → ℝ, Continuous v → MemLp v 2 →
      MemLp (fun p : ℝ × ℝ ↦ v p.1 - v p.2) 2
        (realJumpPairMeasure (fractionalJumpMeasure θ)) →
      v z = 0 → (∀ y ∈ S, v y = 0) →
      realNonlocalPairing volume (realJumpPairMeasure (fractionalJumpMeasure θ)) h v = 0)
    (x : ℝ) : 0 ≤ h x ∧ h x ≤ normalizedBesselKernel θ (x - z) := by
  let κ := fractionalJumpMeasure θ
  have gc : Continuous (fun x ↦ normalizedBesselKernel θ (x - z)) :=
    (continuous_normalizedBesselKernel hθ).comp (continuous_id.sub continuous_const)
  have hg : MemLp (fun x ↦ normalizedBesselKernel θ (x - z)) 2 := by
    simpa only [sub_eq_add_neg, Function.comp_def] using
      (memLp_two_normalizedBesselKernel hθ).comp_measurePreserving
        (measurePreserving_add_right (volume : Measure ℝ) (-z))
  have gJ : MemLp (fun p : ℝ × ℝ ↦ normalizedBesselKernel θ (p.1 - z) -
      normalizedBesselKernel θ (p.2 - z)) 2 (realJumpPairMeasure κ) := by
    simpa only [sub_eq_add_neg] using memLp_jump_translation κ
      (memLp_jump_normalizedBesselKernel hθ hθ₁) (-z)
  constructor
  · exact nonlocal_cardinal_nonneg (realJumpPairMeasure κ) S z hc hh hJ hz hS horth x
  · apply nonlocal_cardinal_le_green (realJumpPairMeasure κ) S z hc gc hh hg hJ gJ hz
      (by simp only [sub_self, normalizedBesselKernel_zero hθ]) hS
      (fun y ↦ (normalizedBesselKernel_pos hθ (y - z)).le) horth
    intro v vc hv vJ hvz
    rw [realNonlocalPairing_translatedBesselKernel hθ hθ₁ z vc hv vJ, hvz, mul_zero]

end RiemannMasullo
