module

public import Mathlib.Probability.Distributions.Gaussian.Real
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import RiemannMasullo.ForMathlib.Analysis.Fourier.JumpForm
import RiemannMasullo.ForMathlib.Analysis.SpecialFunctions.Pow.ShiftedLaplace

/-! # The tempered Gaussian mixture for the fractional Sobolev jump form -/

public noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal FourierTransform SchwartzMap

namespace RiemannMasullo

private def jumpWeight (s u : ℝ) : ℝ :=
  s / Real.Gamma (1 - s) * Real.exp (-u) * u ^ (-s - 1)

private def heatDisplacement (z : ℝ × ℝ) : ℝ :=
  Real.sqrt (2 * z.1) * z.2

private theorem continuous_heatDisplacement : Continuous heatDisplacement := by
  unfold heatDisplacement
  fun_prop

/-- The tempered jump measure, obtained by mixing centered Gaussians of
variance (2u) with the tempered fractional-power weight on (u>0). -/
def temperedJumpMeasure (s : ℝ) : Measure ℝ :=
  ((((volume : Measure ℝ).restrict (Ioi 0)).withDensity
    (fun u ↦ ENNReal.ofReal (jumpWeight s u))).prod (gaussianReal 0 1)).map heatDisplacement

private theorem sFinite_temperedJumpMeasure (s : ℝ) : SFinite (temperedJumpMeasure s) := by
  unfold temperedJumpMeasure
  infer_instance

private theorem lintegral_temperedJumpMeasure (s : ℝ) {f : ℝ → ℝ≥0∞} (hf : Measurable f) :
    (∫⁻ h, f h ∂temperedJumpMeasure s) =
      ∫⁻ u in Ioi (0 : ℝ), ENNReal.ofReal (jumpWeight s u) *
        (∫⁻ y, f (heatDisplacement (u, y)) ∂gaussianReal 0 1) := by
  have hw : Measurable (fun u ↦ ENNReal.ofReal (jumpWeight s u)) := by
    unfold jumpWeight
    fun_prop
  have hfg : Measurable (f ∘ heatDisplacement) := hf.comp continuous_heatDisplacement.measurable
  unfold temperedJumpMeasure
  rw [lintegral_map hf continuous_heatDisplacement.measurable]
  change (∫⁻ z, (f ∘ heatDisplacement) z
    ∂((volume.restrict (Ioi (0 : ℝ))).withDensity
      (fun u ↦ ENNReal.ofReal (jumpWeight s u))).prod (gaussianReal 0 1)) = _
  rw [lintegral_prod _ hfg.aemeasurable,
    lintegral_withDensity_eq_lintegral_mul _ hw hfg.lintegral_prod_right']
  rfl

private theorem jumpWeight_nonneg {s u : ℝ} (hs : 0 < s) (hs' : s < 1) (hu : 0 < u) :
    0 ≤ jumpWeight s u := by
  unfold jumpWeight
  have hG := Real.Gamma_pos_of_pos (sub_pos.mpr hs')
  positivity

private theorem gaussian_characterDifference_lintegral {u : ℝ} (hu : 0 < u) (ξ : ℝ) :
    (∫⁻ y, ENNReal.ofReal (‖(𝐞 (heatDisplacement (u, y) * ξ) : ℂ) - 1‖ ^ 2)
      ∂gaussianReal 0 1) =
      2 * ENNReal.ofReal (1 - Real.exp (-(u * (2 * Real.pi * ξ) ^ 2))) := by
  let F (y : ℝ) := (𝐞 (heatDisplacement (u, y) * ξ) : ℂ)
  have hn (y : ℝ) : ‖F y‖ = 1 := Circle.norm_coe _
  have hf : Continuous F :=
    (continuous_subtype_val.comp Real.continuous_fourierChar).comp
      ((continuous_heatDisplacement.comp (continuous_const.prodMk continuous_id)).mul_const ξ)
  have hi : Integrable F (gaussianReal 0 1) :=
    Integrable.of_bound hf.aestronglyMeasurable 1 (ae_of_all _ fun y ↦ (hn y).le)
  let k := Real.sqrt (2 * u) * (2 * Real.pi * ξ)
  have hchar : (∫ y, F y ∂gaussianReal 0 1) =
      (Real.exp (-(u * (2 * Real.pi * ξ) ^ 2)) : ℂ) := by
    calc
      _ = charFun (gaussianReal 0 1) k := by
        rw [charFun_apply_real]
        refine integral_congr_ae (ae_of_all _ fun y ↦ ?_)
        simp only [F, heatDisplacement, Real.fourierChar_apply, k]
        push_cast
        ring_nf
      _ = _ := by
        rw [charFun_gaussianReal, Complex.ofReal_exp]
        congr 1
        have hk : k ^ 2 = 2 * u * (2 * Real.pi * ξ) ^ 2 := by
          dsimp only [k]
          rw [mul_pow, Real.sq_sqrt (by positivity : 0 ≤ 2 * u)]
        norm_num
        rw [← Complex.ofReal_pow, hk]
        push_cast
        ring
  have he (y : ℝ) : ‖F y - 1‖ ^ 2 = 2 * (1 - (F y).re) :=
    Complex.norm_sub_one_sq_eq_of_norm_eq_one (hn y)
  have hint : Integrable (fun y ↦ ‖F y - 1‖ ^ 2) (gaussianReal 0 1) :=
    (((integrable_const (1 : ℝ)).sub hi.re).const_mul 2).congr (ae_of_all _ fun y ↦ (he y).symm)
  change (∫⁻ y, ENNReal.ofReal (‖F y - 1‖ ^ 2) ∂gaussianReal 0 1) = _
  rw [← ofReal_integral_eq_lintegral_ofReal hint (ae_of_all _ fun _ ↦ sq_nonneg _)]
  simp_rw [he]
  have hiRe : Integrable (fun y ↦ (F y).re) (gaussianReal 0 1) := hi.re
  have heRe : (∫ y, (F y).re ∂gaussianReal 0 1) = (∫ y, F y ∂gaussianReal 0 1).re :=
    integral_re hi
  rw [integral_const_mul, integral_sub (integrable_const (1 : ℝ)) hiRe, heRe, hchar]
  simp only [integral_const, probReal_univ, one_smul, Complex.ofReal_re,
    ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2), ENNReal.ofReal_ofNat]


/-- The tempered Gaussian jump measure has the shifted fractional Sobolev symbol. -/
theorem temperedJumpMeasure_symbol {s : ℝ} (hs : 0 < s) (hs' : s < 1) (ξ : ℝ) :
    (2 : ℝ≥0∞)⁻¹ *
        (∫⁻ h, ENNReal.ofReal (‖(𝐞 (h * ξ) : ℂ) - 1‖ ^ 2) ∂temperedJumpMeasure s) =
      ENNReal.ofReal ((1 + (2 * Real.pi * ξ) ^ 2) ^ s - 1) := by
  let a := (2 * Real.pi * ξ) ^ 2
  let f (h : ℝ) := ENNReal.ofReal (‖(𝐞 (h * ξ) : ℂ) - 1‖ ^ 2)
  let w (u : ℝ) := ENNReal.ofReal (jumpWeight s u)
  have hf : Measurable f := ENNReal.measurable_ofReal.comp
    (by fun_prop : Continuous (fun h ↦ ‖(𝐞 (h * ξ) : ℂ) - 1‖ ^ 2)).measurable
  change 2⁻¹ * (∫⁻ h, f h ∂temperedJumpMeasure s) = ENNReal.ofReal ((1 + a) ^ s - 1)
  rw [lintegral_temperedJumpMeasure s hf, ← lintegral_const_mul' _ _ (by simp)]
  refine Eq.trans (lintegral_congr_ae ?_) (lintegral_tempered_laplace_difference hs hs' (sq_nonneg _))
  filter_upwards [ae_restrict_mem (μ := volume) (measurableSet_Ioi (a := (0 : ℝ)))] with u hu
  have hu' : 0 < u := hu
  change 2⁻¹ * (w u * (∫⁻ y, f (heatDisplacement (u, y)) ∂gaussianReal 0 1)) =
    ENNReal.ofReal (jumpWeight s u * (1 - Real.exp (-(u * a))))
  rw [show (∫⁻ y, f (heatDisplacement (u, y)) ∂gaussianReal 0 1) =
      2 * ENNReal.ofReal (1 - Real.exp (-(u * a))) from
    gaussian_characterDifference_lintegral hu' ξ]
  rw [mul_left_comm (2 : ℝ≥0∞)⁻¹, ← mul_assoc (2 : ℝ≥0∞)⁻¹ 2,
    ENNReal.inv_mul_cancel two_ne_zero ENNReal.ofNat_ne_top, one_mul]
  exact (ENNReal.ofReal_mul (jumpWeight_nonneg hs hs' hu')).symm

/-- The Schwartz fractional Sobolev energy is precisely the mass plus the
tempered Gaussian mixture of squared translation differences. -/
theorem schwartz_fractional_energy_eq_tempered_jump (f : 𝓢(ℝ, ℂ)) {s : ℝ}
    (hs : 0 < s) (hs' : s < 1) :
    (∫⁻ x, ENNReal.ofReal (‖f x‖ ^ 2)) + (2 : ℝ≥0∞)⁻¹ *
        (∫⁻ h, (∫⁻ x, ENNReal.ofReal (‖f (x + h) - f x‖ ^ 2)) ∂temperedJumpMeasure s) =
      ∫⁻ ξ, ENNReal.ofReal ((1 + (2 * Real.pi * ξ) ^ 2) ^ s) *
        ENNReal.ofReal (‖𝓕 f ξ‖ ^ 2) := by
  let _ := sFinite_temperedJumpMeasure s
  exact schwartz_fractional_energy_eq_of_jump_symbol f s hs.le (temperedJumpMeasure s)
    (temperedJumpMeasure_symbol hs hs')

/-- The tempered jump energy equals the fractional Fourier energy on logarithmic L².
The equality includes the case of infinite energy. -/
theorem lineL2_fractional_energy_eq_tempered_jump (f : Lp ℂ 2 (volume : Measure ℝ)) {s : ℝ}
    (hs : 0 < s) (hs' : s < 1) :
    (∫⁻ x, ENNReal.ofReal (‖f x‖ ^ 2)) + (2 : ℝ≥0∞)⁻¹ *
        (∫⁻ h, (∫⁻ x, ENNReal.ofReal (‖f (x + h) - f x‖ ^ 2)) ∂temperedJumpMeasure s) =
      ∫⁻ ξ, ENNReal.ofReal ((1 + (2 * Real.pi * ξ) ^ 2) ^ s) *
        ENNReal.ofReal (‖(𝓕 f) ξ‖ ^ 2) := by
  let _ := sFinite_temperedJumpMeasure s
  exact lineL2_fractional_energy_eq_of_jump_symbol f s hs.le (temperedJumpMeasure s)
    (temperedJumpMeasure_symbol hs hs')

private theorem gaussian_secondMoment_lintegral {u : ℝ} (hu : 0 < u) :
    (∫⁻ y, ENNReal.ofReal ((heatDisplacement (u, y)) ^ 2) ∂gaussianReal 0 1) =
      ENNReal.ofReal (2 * u) := by
  have hi : Integrable (fun y : ℝ ↦ y ^ 2) (gaussianReal 0 1) := by
    simpa [Real.norm_eq_abs, sq_abs] using
      (memLp_id_gaussianReal (μ := 0) (v := 1) 2).integrable_norm_rpow (by norm_num) (by simp)
  have hv := variance_id_gaussianReal (μ := 0) (v := 1)
  rw [variance_eq_integral measurable_id.aemeasurable] at hv
  have hv' : (∫ y : ℝ, y ^ 2 ∂gaussianReal 0 1) = 1 := by
    simpa [integral_id_gaussianReal] using hv
  simp_rw [heatDisplacement, mul_pow, Real.sq_sqrt (by positivity : 0 ≤ 2 * u),
    ENNReal.ofReal_mul (by positivity : 0 ≤ 2 * u)]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
    ← ofReal_integral_eq_lintegral_ofReal hi (ae_of_all _ fun _ ↦ sq_nonneg _), hv']
  simp

/-- The jump measure has finite second moment (2s). -/
theorem temperedJumpMeasure_secondMoment {s : ℝ} (hs : 0 < s) (hs' : s < 1) :
    (∫⁻ h, ENNReal.ofReal (h ^ 2) ∂temperedJumpMeasure s) = ENNReal.ofReal (2 * s) := by
  rw [lintegral_temperedJumpMeasure s (by fun_prop)]
  refine (lintegral_congr_ae ?_).trans (lintegral_tempered_laplace_mul_twice hs hs')
  filter_upwards [ae_restrict_mem (μ := volume) (measurableSet_Ioi (a := (0 : ℝ)))] with u hu
  have hu' : 0 < u := hu
  rw [gaussian_secondMoment_lintegral hu', ← ENNReal.ofReal_mul (jumpWeight_nonneg hs hs' hu')]
  rfl

end RiemannMasullo
