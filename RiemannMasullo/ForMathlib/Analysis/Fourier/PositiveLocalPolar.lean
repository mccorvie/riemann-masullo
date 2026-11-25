module

public import RiemannMasullo.ForMathlib.Analysis.Fourier.StripLaplace
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! # The polar correction for profiles with positive spectrum

For a compact smooth log profile, positivity of the real part of its bilateral Laplace
transform on the critical axis forces positivity of its integral against every bilateral
exponential. At scale one half this is the min-power correction of the rational local trace.
-/

open MeasureTheory Set Complex
open scoped FourierTransform SchwartzMap ContDiff

@[expose] public noncomputable section

namespace RiemannMasullo

private noncomputable def damping (b x : ℝ) : ℂ := (Real.exp (-b * |x|) : ℂ)

private theorem damping_integrable {b : ℝ} (hb : 0 < b) : Integrable (damping b) := by
  have left := integrableOn_exp_mul_Iic hb 0
  have right := integrableOn_exp_mul_Ioi (neg_lt_zero.mpr hb) 0
  have hl : IntegrableOn (fun x : ℝ ↦ Real.exp (-b * |x|)) (Iic 0) :=
    left.congr_fun (fun x hx ↦ by simp [abs_of_nonpos hx]) measurableSet_Iic
  have hr : IntegrableOn (fun x : ℝ ↦ Real.exp (-b * |x|)) (Ioi 0) :=
    right.congr_fun (fun x hx ↦ by simp [abs_of_pos hx]) measurableSet_Ioi
  have hi : Integrable (fun x : ℝ ↦ Real.exp (-b * |x|)) := by simpa using hl.union hr
  exact hi.ofReal (𝕜 := ℂ)

private theorem fourier_damping {b : ℝ} (hb : 0 < b) (t : ℝ) :
    𝓕 (damping b) t = ((2 * b / (b ^ 2 + (2 * Real.pi * t) ^ 2) : ℝ) : ℂ) := by
  let w := 2 * Real.pi * t
  let l : ℂ := b - (w : ℂ) * I
  let r : ℂ := -b - (w : ℂ) * I
  have hl : 0 < l.re := by simpa [l] using hb
  have hr : r.re < 0 := by simpa [r] using neg_lt_zero.mpr hb
  let f (x : ℝ) := exp ((↑(-2 * Real.pi * x * t) : ℂ) * I) * damping b x
  have lf (x : ℝ) (hx : x ∈ Iic 0) : f x = exp (l * x) := by
    dsimp [f, damping, l, w]
    rw [Complex.ofReal_exp, ← exp_add, abs_of_nonpos hx]
    congr 1
    push_cast
    ring
  have rf (x : ℝ) (hx : x ∈ Ioi 0) : f x = exp (r * x) := by
    dsimp [f, damping, r, w]
    rw [Complex.ofReal_exp, ← exp_add, abs_of_pos hx]
    congr 1
    push_cast
    ring
  have il := (integrableOn_exp_mul_complex_Iic hl 0).congr_fun (fun x hx ↦ (lf x hx).symm) measurableSet_Iic
  have ir := (integrableOn_exp_mul_complex_Ioi hr 0).congr_fun (fun x hx ↦ (rf x hx).symm) measurableSet_Ioi
  rw [Real.fourier_real_eq_integral_exp_smul]
  change (∫ x, f x) = _
  rw [← intervalIntegral.integral_Iic_add_Ioi il ir, setIntegral_congr_fun measurableSet_Iic lf,
    setIntegral_congr_fun measurableSet_Ioi rf, integral_exp_mul_complex_Iic hl, integral_exp_mul_complex_Ioi hr]
  simp only [Complex.ofReal_zero, mul_zero, exp_zero]
  have h₁ : l ≠ 0 := fun e ↦ by simp [e] at hl
  have h₂ : r ≠ 0 := fun e ↦ by simp [e] at hr
  change _ = ((2 * b/(b ^ 2+w^2) : ℝ) : ℂ)
  have h₃ : ((b:ℂ)^2+(w:ℂ)^2) ≠ 0 := by exact_mod_cast (show (0:ℝ)<b ^ 2+w^2 by positivity).ne'
  push_cast
  field_simp [h₁, h₂, h₃]
  dsimp [l,r]
  ring_nf
  simp [I_sq]

/-- The bilateral exponential weights the real Fourier spectrum by a positive Cauchy kernel. -/
private theorem damping_integral_eq (H : 𝓢(ℝ, ℂ)) {b : ℝ} (hb : 0 < b) :
    (∫ x : ℝ, damping b x * H x) =
      ∫ t : ℝ, ((2 * b/(b ^ 2+(2 * Real.pi * t) ^ 2) : ℝ) : ℂ) * (𝓕 H) t := by
  have he := VectorFourier.integral_fourierIntegral_smul_eq_flip (L := innerₗ ℝ)
    Real.continuous_fourierChar continuous_inner (damping_integrable hb) ((𝓕 H).integrable (μ := (volume : Measure ℝ)))
  rw [flip_innerₗ] at he
  change (∫ t : ℝ, 𝓕 (damping b) t * (𝓕 H) t) =
      ∫ x : ℝ, damping b x * 𝓕 ((𝓕 H : 𝓢(ℝ, ℂ)) : ℝ → ℂ) x at he
  have hdouble (x : ℝ) : 𝓕 ((𝓕 H : 𝓢(ℝ, ℂ)) : ℝ → ℂ) x = H (-x) := by
    have h := Real.fourierInv_eq_fourier_neg ((𝓕 H : 𝓢(ℝ, ℂ)) : ℝ → ℂ) (-x)
    rw [neg_neg, ← SchwartzMap.fourierInv_coe, FourierTransform.fourierInv_fourier_eq] at h
    exact h.symm
  simp only [fourier_damping hb, hdouble] at he
  rw [he, ← integral_neg_eq_self (fun x : ℝ ↦ damping b x * H (-x)) volume]
  simp [damping]

/-- Positive real Fourier spectrum gives a strictly positive physical polar defect. -/
private theorem damping_integral_re_pos (H : 𝓢(ℝ, ℂ)) (hH : ∀ t : ℝ, 0 < ((𝓕 H) t).re)
    {b : ℝ} (hb : 0 < b) : 0 < (∫ x : ℝ, damping b x * H x).re := by
  let FH : 𝓢(ℝ, ℂ) := 𝓕 H
  let k (t : ℝ) := 2 * b/(b ^ 2+(2 * Real.pi * t) ^ 2)
  have hk (t : ℝ) : 0 < k t := by dsimp [k]; positivity
  have hbound (t : ℝ) : k t ≤ 2 / b := by
    dsimp [k]
    apply (div_le_div_iff₀ (by positivity) hb).mpr
    nlinarith [sq_nonneg (2 * Real.pi * t)]
  have hc : Continuous k := by
    exact continuous_const.div (by fun_prop) (fun t ↦ (by positivity : 0 < b ^ 2+(2 * Real.pi * t) ^ 2).ne')
  have hi : Integrable (fun t : ℝ ↦ ((k t : ℝ) : ℂ) * FH t) := by
    apply ((FH.integrable (μ := (volume : Measure ℝ))).norm.const_mul (2 / b)).mono'
    · exact (Complex.continuous_ofReal.comp hc).aestronglyMeasurable.mul FH.continuous.aestronglyMeasurable
    · filter_upwards with t
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (hk t).le]
      exact mul_le_mul_of_nonneg_right (hbound t) (norm_nonneg _)
  rw [damping_integral_eq H hb]
  change 0 < (∫ t : ℝ, (k t : ℂ) * FH t).re
  rw [← RCLike.re_eq_complex_re, ← integral_re hi]
  change 0 < ∫ t : ℝ, ((k t : ℂ) * FH t).re
  have hp (t : ℝ) : 0 < ((k t : ℂ) * FH t).re := by
    rw [Complex.re_ofReal_mul]
    exact mul_pos (hk t) (hH t)
  apply (integral_pos_iff_support_of_nonneg (fun t ↦ (hp t).le) hi.re).2
  have hs : Function.support (fun t : ℝ ↦ ((k t : ℂ) * FH t).re) = Set.univ := by
    apply Set.eq_univ_of_forall
    intro t
    exact (hp t).ne'
  rw [hs]
  simp

/-- A compact smooth log profile whose bilateral Laplace transform is positive on
the imaginary axis has a strictly positive min-power polar correction at every scale. -/
theorem integral_exp_neg_abs_mul_pos_of_bilateralLaplace (H : ℝ → ℝ)
    (hc : HasCompactSupport H) (hs : ContDiff ℝ ∞ H)
    (hpos : ∀ t : ℝ, 0 < (bilateralLaplace (fun x ↦ (H x : ℂ)) (t * I)).re)
    {b : ℝ} (hb : 0 < b) : 0 < ∫ x : ℝ, Real.exp (-b * |x|) * H x := by
  let u : 𝓢(ℝ, ℂ) := (hc.comp_left Complex.ofReal_zero).toSchwartzMap (Complex.ofRealCLM.contDiff.comp hs)
  have hu (x : ℝ) : u x = (H x : ℂ) := rfl
  have hfreq (t : ℝ) : ((𝓕 u) t) =
      RiemannMasullo.bilateralLaplace (fun x ↦ (H x : ℂ)) ((-2 * Real.pi * t : ℝ) * I) := by
    rw [SchwartzMap.fourier_coe, Real.fourier_real_eq_integral_exp_smul]
    unfold RiemannMasullo.bilateralLaplace
    apply integral_congr_ae
    filter_upwards with x
    rw [smul_eq_mul, hu, mul_comm (H x : ℂ)]
    congr 2
    push_cast
    ring
  have pos := damping_integral_re_pos u (fun t ↦ (hfreq t) ▸ hpos _) hb
  have hrep : (fun x : ℝ ↦ damping b x * u x) =
      (fun x : ℝ ↦ ((Real.exp (-b * |x|) * H x : ℝ) : ℂ)) := by
    funext x
    rw [Complex.ofReal_mul, hu]
    rfl
  rw [hrep, integral_complex_ofReal, Complex.ofReal_re] at pos
  exact pos

end RiemannMasullo
