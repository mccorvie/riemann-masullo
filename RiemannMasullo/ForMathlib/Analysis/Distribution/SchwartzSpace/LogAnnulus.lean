module
public import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
public import Mathlib.Analysis.Calculus.Deriv.Abs
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper
public import Mathlib.MeasureTheory.Measure.Lebesgue.Integral
public import Mathlib.Analysis.MellinTransform

@[expose] public noncomputable section
open MeasureTheory Set Function Filter
open scoped SchwartzMap ContDiff Topology FourierTransform
namespace RiemannMasullo

/-- A compact smooth log profile is realized by an even Schwartz function
supported in a compact annulus, including the inverse multiplicative Jacobian. -/
theorem exists_schwartz_log_annulus (H : 𝓢(ℝ, ℂ)) (hH : HasCompactSupport (H : ℝ → ℂ)) :
    ∃ h : 𝓢(ℝ, ℂ), HasCompactSupport (h : ℝ → ℂ) ∧ h 0 = 0 ∧
      (∀ r, h (-r) = h r) ∧ ∀ r, h r = (|r|⁻¹ : ℝ) • H (Real.log |r|) := by
  let f (r : ℝ) : ℂ := (|r|⁻¹ : ℝ) • H (Real.log |r|)
  obtain ⟨a, ha⟩ := hH.bddBelow
  obtain ⟨b, hb⟩ := hH.bddAbove
  have hzero (r : ℝ) (hr : |r| < Real.exp a) : f r = 0 := by
    by_cases hr0 : r = 0
    · simp [f, hr0]
    have hlog : Real.log |r| < a := (Real.log_lt_iff_lt_exp (abs_pos.mpr hr0)).mpr hr
    have hHz : H (Real.log |r|) = 0 := by
      by_contra hn
      exact (not_le_of_gt hlog) (ha (subset_tsupport _ hn))
    simp only [f, hHz, smul_zero]
  have hs : ContDiff ℝ ∞ f := by
    apply contDiff_iff_contDiffAt.mpr
    intro r
    by_cases hr : r = 0
    · subst r
      apply (contDiffAt_const (c := (0 : ℂ))).congr_of_eventuallyEq
      filter_upwards [Metric.ball_mem_nhds (0 : ℝ) (Real.exp_pos a)] with x hx
      exact hzero x (by simpa only [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs] using hx)
    · exact ((contDiffAt_abs hr).inv (abs_ne_zero.mpr hr)).smul
        ((H.smooth ⊤).contDiffAt.comp r ((contDiffAt_abs hr).log (abs_ne_zero.mpr hr)))
  have hc : HasCompactSupport f := by
    apply HasCompactSupport.of_support_subset_isCompact (K := Icc (-Real.exp b) (Real.exp b)) isCompact_Icc
    intro r hr
    have hr0 : r ≠ 0 := by intro hh; subst r; simp [mem_support, f] at hr
    have hHz : H (Real.log |r|) ≠ 0 := by
      intro hz
      apply hr
      change (|r|⁻¹ : ℝ) • H (Real.log |r|) = 0
      rw [hz, smul_zero]
    have hbound : |r| ≤ Real.exp b := (Real.log_le_iff_le_exp (abs_pos.mpr hr0)).mp
      (hb (subset_tsupport _ hHz))
    exact abs_le.mp hbound
  refine ⟨hc.toSchwartzMap hs, hc, by simp [f], fun r ↦ ?_, fun _ ↦ rfl⟩
  change f (-r) = f r
  simp only [f, abs_neg]

/-- The Mellin transform of an inverse-Jacobian log profile is its bilateral
Laplace transform with the exponent shifted by one. -/
theorem mellin_log_annulus (H : ℝ → ℂ) (s : ℂ) :
    mellin (fun r : ℝ ↦ (|r|⁻¹ : ℝ) • H (Real.log |r|)) s =
      ∫ x : ℝ, Complex.exp ((s - 1) * (x : ℂ)) * H x := by
  rw [mellin, ← integral_comp_exp]
  apply integral_congr_ae (.of_forall fun x ↦ ?_)
  simp only [abs_of_pos (Real.exp_pos x), Real.log_exp, Complex.real_smul, smul_eq_mul,
    Complex.ofReal_inv]
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr (Real.exp_ne_zero x)),
    ← Complex.ofReal_log (Real.exp_pos x).le, Real.log_exp]
  rw [mul_comm (x : ℂ) (s - 1)]
  field_simp

private theorem integral_even_complex {f : ℝ → ℂ} (hf : Integrable f)
    (he : ∀ x, f (-x) = f x) : (∫ x, f x) = 2 * ∫ x in Ioi 0, f x := by
  have hn : (∫ x in Iic (0 : ℝ), f x) = ∫ x in Ioi (0 : ℝ), f x := by
    simpa only [he, neg_zero] using integral_comp_neg_Iic 0 f
  rw [← intervalIntegral.integral_Iic_add_Ioi (b := (0 : ℝ)) hf.integrableOn hf.integrableOn, hn]
  ring

/-- The full additive mass of an even annular lift is twice the log-profile mass. -/
theorem integral_log_annulus (H h : 𝓢(ℝ, ℂ))
    (hh : ∀ r, h r = (|r|⁻¹ : ℝ) • H (Real.log |r|)) :
    (∫ r, h r) = 2 * ∫ x, H x := by
  have he (r : ℝ) : h (-r) = h r := by rw [hh, hh, abs_neg]
  rw [integral_even_complex h.integrable he, ← integral_comp_exp]
  congr 1
  apply integral_congr_ae (.of_forall fun x ↦ ?_)
  rw [hh, abs_of_pos (Real.exp_pos x), Real.log_exp, smul_smul,
    mul_inv_cancel₀ (Real.exp_ne_zero x), one_smul]

/-- The imaginary Mellin line is the real Fourier transform of the log profile. -/
theorem mellin_log_annulus_fourier (H : ℝ → ℂ) (ξ : ℝ) :
    mellin (fun r : ℝ ↦ (|r|⁻¹ : ℝ) • H (Real.log |r|))
      (1 - (2 * Real.pi * ξ : ℝ) * Complex.I) = 𝓕 H ξ := by
  rw [mellin_log_annulus, Real.fourier_real_eq_integral_exp_smul]
  apply integral_congr_ae (.of_forall fun x ↦ ?_)
  rw [smul_eq_mul]
  congr 2
  push_cast
  ring

/-- The full logarithmic moment of an even annular lift is twice the first
additive moment of its log profile. -/
theorem logMoment_log_annulus (H h : 𝓢(ℝ, ℂ)) (hH : HasCompactSupport (H : ℝ → ℂ))
    (hh : ∀ r, h r = (|r|⁻¹ : ℝ) • H (Real.log |r|)) :
    (∫ r, (Real.log r : ℂ) * h r) = 2 * ∫ x : ℝ, (x : ℂ) * H x := by
  let XH := SchwartzMap.smulLeftCLM (𝕜 := ℝ) ℂ (fun x : ℝ ↦ x) H
  have hXH (x : ℝ) : XH x = (x : ℂ) * H x := by
    rw [SchwartzMap.smulLeftCLM_apply_apply (show (fun x : ℝ ↦ x).HasTemperateGrowth by fun_prop)]
    rfl
  have hc : HasCompactSupport (XH : ℝ → ℂ) := by
    rw [show (XH : ℝ → ℂ) = fun x : ℝ ↦ (x : ℂ) * H x from funext hXH]
    exact hH.mul_left
  obtain ⟨g, -, -, -, hg⟩ := exists_schwartz_log_annulus XH hc
  have he (r : ℝ) : g r = (Real.log r : ℂ) * h r := by
    rw [hg, hh, hXH, Real.log_abs]
    simp only [Complex.real_smul]
    ring
  calc
    _ = ∫ r, g r := integral_congr_ae (.of_forall fun r ↦ (he r).symm)
    _ = 2 * ∫ x, XH x := integral_log_annulus XH g hg
    _ = _ := by simp_rw [hXH]

end RiemannMasullo
