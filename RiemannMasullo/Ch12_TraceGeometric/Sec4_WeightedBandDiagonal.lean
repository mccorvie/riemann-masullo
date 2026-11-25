module

public import RiemannMasullo.Ch12_TraceGeometric.Sec4_WeightedBandKernel
public import RiemannMasullo.Ch12_TraceGeometric.Sec4_RealPWLevelTrace
import Mathlib.Analysis.Fourier.Inversion
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.Prod

/-! # The weighted band of the rational real-place model: the diagonal integral and its limit

Paper: Theorem 12.4.1.1, pp. 514–519, and the value used on p. 520.

In the picture of `Sec4_WeightedBandKernel` the trace over the odd band of the cutoff dilation
with its multiplier is `g ^ (-1/2) ∫ z in -L..L, r_g z * K (z / g, z)`, with `K` the kernel of
the odd band and `r_g` the multiplier. This file computes the limit of that integral as
`L → ∞`.

* `integral_cexp_div_sq_add_sq`: the Fourier transform of the Lorentzian, for a complex
  parameter `a` of positive real part: `∫ exp (2 π i t x) / (x ^ 2 + a ^ 2) dx` is
  `(π / a) exp (-2 π a |t|)`. It follows from Fourier inversion applied to the two-sided
  exponential `ξ ↦ exp (-2 π a |ξ|)`.
* `integral_realBandKernel_mul_div_sq_add_sq`: the integral of the band kernel along a ray
  against the Lorentzian, `∫ S (c x) / (x ^ 2 + a ^ 2) dx = (1 - exp (-2 π a c Y)) / (a ^ 2 c)`.
* `tendsto_integral_weightedDilationMultiplier_mul_realOddBandKernel`: the limit is
  `g ^ (3/2) / (g ^ 2 - 1) - g ^ (-1/2) + weightedBandDefect Y g`, for every `Y > 0` and
  `g > 1`.

The multiplier is the constant `g` plus a rational function that is integrable on the line. The
constant gives the first term through the conditionally convergent integral of `sinc`. The
rational part gives `-g ^ (-1/2)` and the term `weightedBandDefect Y g`, through the second
lemma at `a = -i g ζ`, whose square is `-i g ^ 2`.
-/

open MeasureTheory Real Set Filter Topology
open scoped FourierTransform

@[expose] public noncomputable section

namespace RiemannMasullo

/-! ### The Fourier transform of the Lorentzian -/

/-- For `a` of positive real part and real `x`, `x ^ 2 + a ^ 2` is not zero. -/
theorem ofReal_sq_add_sq_ne_zero {a : ℂ} (ha : 0 < a.re) (x : ℝ) : (x : ℂ) ^ 2 + a ^ 2 ≠ 0 := by
  have h : (x : ℂ) ^ 2 + a ^ 2 = (a + Complex.I * x) * (a - Complex.I * x) := by
    ring_nf
    rw [Complex.I_sq]
    ring
  rw [h]
  refine mul_ne_zero (fun h0 ↦ ?_) (fun h0 ↦ ?_)
  · have := congrArg Complex.re h0
    simp at this
    linarith
  · have := congrArg Complex.re h0
    simp at this
    linarith

/-- The two-sided exponential `ξ ↦ exp (-2 π a |ξ|)` is integrable when `a` has positive real
part. -/
theorem integrable_cexp_neg_mul_abs {a : ℂ} (ha : 0 < a.re) :
    Integrable fun ξ : ℝ ↦ Complex.exp (-(2 * π * a) * (|ξ| : ℝ)) := by
  have h1 : IntegrableOn (fun ξ : ℝ ↦ Complex.exp (-(2 * π * a) * (|ξ| : ℝ))) (Ioi 0) := by
    refine (integrableOn_exp_mul_complex_Ioi (a := -(2 * π * a)) ?_ 0).congr_fun
      (fun ξ hξ ↦ ?_) measurableSet_Ioi
    · simp only [Complex.neg_re, Complex.mul_re, Complex.re_ofNat, Complex.ofReal_re,
        Complex.im_ofNat, Complex.ofReal_im, mul_zero, sub_zero, Complex.mul_im, zero_mul,
        add_zero]
      nlinarith [pi_pos]
    · simp only [abs_of_pos (mem_Ioi.mp hξ)]
  have h2 : IntegrableOn (fun ξ : ℝ ↦ Complex.exp (-(2 * π * a) * (|ξ| : ℝ))) (Iic 0) := by
    refine (integrableOn_exp_mul_complex_Iic (a := 2 * π * a) ?_ 0).congr_fun
      (fun ξ hξ ↦ ?_) measurableSet_Iic
    · simp only [Complex.mul_re, Complex.re_ofNat, Complex.ofReal_re,
        Complex.im_ofNat, Complex.ofReal_im, mul_zero, sub_zero, Complex.mul_im, zero_mul,
        add_zero]
      nlinarith [pi_pos]
    · simp only [abs_of_nonpos (mem_Iic.mp hξ)]
      push_cast
      ring_nf
  have h := h2.union h1
  rwa [Iic_union_Ioi, integrableOn_univ] at h

/-- The Fourier transform of the two-sided exponential `ξ ↦ exp (-2 π a |ξ|)` is the Lorentzian
`x ↦ a / (π (x ^ 2 + a ^ 2))`. -/
theorem fourier_cexp_neg_mul_abs {a : ℂ} (ha : 0 < a.re) (x : ℝ) :
    𝓕 (fun ξ : ℝ ↦ Complex.exp (-(2 * π * a) * (|ξ| : ℝ))) x =
      a / (π * ((x : ℂ) ^ 2 + a ^ 2)) := by
  have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast pi_ne_zero
  have hp : a + Complex.I * x ≠ 0 := fun h0 ↦ by
    have := congrArg Complex.re h0
    simp at this
    linarith
  have hm : a - Complex.I * x ≠ 0 := fun h0 ↦ by
    have := congrArg Complex.re h0
    simp at this
    linarith
  rw [Real.fourier_real_eq_integral_exp_smul]
  have hint : Integrable fun v : ℝ ↦ Complex.exp (((-2 * π * v * x : ℝ) : ℂ) * Complex.I) •
      Complex.exp (-(2 * π * a) * (|v| : ℝ)) := by
    refine (integrable_cexp_neg_mul_abs ha).bdd_mul (c := 1) ?_ (ae_of_all _ fun v ↦ ?_)
    · exact (by fun_prop : Continuous fun v : ℝ ↦
        Complex.exp (((-2 * π * v * x : ℝ) : ℂ) * Complex.I)).aestronglyMeasurable
    · rw [Complex.norm_exp_ofReal_mul_I]
  rw [← integral_add_compl (measurableSet_Ioi (a := (0 : ℝ))) hint, compl_Ioi]
  have e1 : ∫ v in Ioi (0 : ℝ), Complex.exp (((-2 * π * v * x : ℝ) : ℂ) * Complex.I) •
      Complex.exp (-(2 * π * a) * (|v| : ℝ)) =
      ∫ v in Ioi (0 : ℝ), Complex.exp (-(2 * π * (a + Complex.I * x)) * v) := by
    refine setIntegral_congr_fun measurableSet_Ioi fun v hv ↦ ?_
    simp only [abs_of_pos (mem_Ioi.mp hv), smul_eq_mul]
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  have e2 : ∫ v in Iic (0 : ℝ), Complex.exp (((-2 * π * v * x : ℝ) : ℂ) * Complex.I) •
      Complex.exp (-(2 * π * a) * (|v| : ℝ)) =
      ∫ v in Iic (0 : ℝ), Complex.exp (2 * π * (a - Complex.I * x) * v) := by
    refine setIntegral_congr_fun measurableSet_Iic fun v hv ↦ ?_
    simp only [abs_of_nonpos (mem_Iic.mp hv), smul_eq_mul]
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  have r1 : (-(2 * π * (a + Complex.I * x))).re < 0 := by
    simp only [Complex.neg_re, Complex.mul_re, Complex.re_ofNat, Complex.ofReal_re,
      Complex.im_ofNat, Complex.ofReal_im, mul_zero, sub_zero, Complex.mul_im, zero_mul,
      add_zero, Complex.add_re, Complex.I_re, Complex.I_im, one_mul, Complex.add_im]
    nlinarith [pi_pos]
  have r2 : 0 < (2 * π * (a - Complex.I * x)).re := by
    simp only [Complex.mul_re, Complex.re_ofNat, Complex.ofReal_re,
      Complex.im_ofNat, Complex.ofReal_im, mul_zero, sub_zero, Complex.mul_im, zero_mul,
      add_zero, Complex.sub_re, Complex.I_re, Complex.I_im, one_mul, Complex.sub_im]
    nlinarith [pi_pos]
  rw [e1, e2, integral_exp_mul_complex_Ioi r1, integral_exp_mul_complex_Iic r2]
  have hfac : (x : ℂ) ^ 2 + a ^ 2 = (a + Complex.I * x) * (a - Complex.I * x) := by
    ring_nf
    rw [Complex.I_sq]
    ring
  rw [hfac]
  simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero]
  field_simp
  ring

/-- The function `y ↦ 1 / (y ^ 2 + α ^ 2)` is integrable for `α > 0`. -/
private theorem integrable_inv_sq_add_sq_real {α : ℝ} (hα : 0 < α) :
    Integrable fun y : ℝ ↦ (y ^ 2 + α ^ 2)⁻¹ := by
  refine Integrable.mono' (integrable_inv_one_add_sq.const_mul (1 + (α ^ 2)⁻¹))
    (by fun_prop : Measurable fun y : ℝ ↦ (y ^ 2 + α ^ 2)⁻¹).aestronglyMeasurable
    (ae_of_all _ fun y ↦ ?_)
  have hpos : 0 < y ^ 2 + α ^ 2 := by positivity
  rw [Real.norm_of_nonneg (by positivity), ← div_eq_mul_inv, le_div_iff₀ (by positivity),
    inv_mul_le_iff₀ hpos]
  have h1 : (y ^ 2 + α ^ 2) * (1 + (α ^ 2)⁻¹) =
      y ^ 2 + y ^ 2 * (α ^ 2)⁻¹ + α ^ 2 + α ^ 2 * (α ^ 2)⁻¹ := by ring
  have h2 : α ^ 2 * (α ^ 2)⁻¹ = 1 := mul_inv_cancel₀ (by positivity)
  have h3 : 0 ≤ y ^ 2 * (α ^ 2)⁻¹ := by positivity
  rw [h1, h2]
  nlinarith [sq_nonneg α]

/-- The Lorentzian `x ↦ 1 / (x ^ 2 + a ^ 2)` is integrable when `a` has positive real part. -/
theorem integrable_inv_sq_add_sq {a : ℂ} (ha : 0 < a.re) :
    Integrable fun x : ℝ ↦ ((x : ℂ) ^ 2 + a ^ 2)⁻¹ := by
  have hu := integrable_inv_sq_add_sq_real ha
  have hbound : Integrable fun x : ℝ ↦
      1 / 2 * (((x + a.im) ^ 2 + a.re ^ 2)⁻¹ + ((x - a.im) ^ 2 + a.re ^ 2)⁻¹) :=
    ((hu.comp_add_right a.im).add (hu.comp_sub_right a.im)).const_mul (1 / 2)
  refine Integrable.mono' hbound
    (Continuous.inv₀ (by fun_prop) (ofReal_sq_add_sq_ne_zero ha)).aestronglyMeasurable
    (ae_of_all _ fun x ↦ ?_)
  have hfac : (x : ℂ) ^ 2 + a ^ 2 = (x - Complex.I * a) * (x + Complex.I * a) := by
    ring_nf
    rw [Complex.I_sq]
    ring
  have hp : ‖(x : ℂ) - Complex.I * a‖ ^ 2 = (x + a.im) ^ 2 + a.re ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp
    ring
  have hq : ‖(x : ℂ) + Complex.I * a‖ ^ 2 = (x - a.im) ^ 2 + a.re ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp
    ring
  rw [hfac, norm_inv, norm_mul, mul_inv, ← hp, ← hq, ← inv_pow, ← inv_pow]
  nlinarith [sq_nonneg (‖(x : ℂ) - Complex.I * a‖⁻¹ - ‖(x : ℂ) + Complex.I * a‖⁻¹)]

/-- A character over the Lorentzian is integrable. -/
theorem integrable_cexp_div_sq_add_sq {a : ℂ} (ha : 0 < a.re) (t : ℝ) :
    Integrable fun x : ℝ ↦
      Complex.exp (2 * π * Complex.I * t * x) / ((x : ℂ) ^ 2 + a ^ 2) := by
  refine Integrable.mono' (integrable_inv_sq_add_sq ha).norm
    (Continuous.div (by fun_prop) (by fun_prop)
      (ofReal_sq_add_sq_ne_zero ha)).aestronglyMeasurable
    (ae_of_all _ fun x ↦ ?_)
  have he : (2 * π * Complex.I * t * x : ℂ) = ((2 * π * t * x : ℝ) : ℂ) * Complex.I := by
    push_cast
    ring
  rw [norm_div, he, Complex.norm_exp_ofReal_mul_I, one_div, norm_inv]

/-- **The Fourier transform of the Lorentzian.** For `a` of positive real part and real `t`,
`∫ exp (2 π i t x) / (x ^ 2 + a ^ 2) dx = (π / a) exp (-2 π a |t|)`. -/
theorem integral_cexp_div_sq_add_sq {a : ℂ} (ha : 0 < a.re) (t : ℝ) :
    ∫ x : ℝ, Complex.exp (2 * π * Complex.I * t * x) / ((x : ℂ) ^ 2 + a ^ 2) =
      π / a * Complex.exp (-(2 * π * a) * (|t| : ℝ)) := by
  have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast pi_ne_zero
  have ha0 : a ≠ 0 := fun h ↦ by simp [h] at ha
  have hf := integrable_cexp_neg_mul_abs ha
  have hc : Continuous fun ξ : ℝ ↦ Complex.exp (-(2 * π * a) * (|ξ| : ℝ)) := by fun_prop
  have hF : 𝓕 (fun ξ : ℝ ↦ Complex.exp (-(2 * π * a) * (|ξ| : ℝ))) =
      fun x : ℝ ↦ a / (π * ((x : ℂ) ^ 2 + a ^ 2)) := funext (fourier_cexp_neg_mul_abs ha)
  have hFi : Integrable (𝓕 (fun ξ : ℝ ↦ Complex.exp (-(2 * π * a) * (|ξ| : ℝ)))) := by
    rw [hF]
    refine ((integrable_inv_sq_add_sq ha).const_mul (a / π)).congr (ae_of_all _ fun x ↦ ?_)
    have := ofReal_sq_add_sq_ne_zero ha x
    field_simp
  have hinv := congrFun (hc.fourierInv_fourier_eq hf hFi) t
  rw [hF, Real.fourierInv_eq_fourier_neg, Real.fourier_real_eq_integral_exp_smul] at hinv
  rw [← hinv, ← integral_const_mul]
  refine integral_congr_ae (ae_of_all _ fun x ↦ ?_)
  have := ofReal_sq_add_sq_ne_zero ha x
  have he : Complex.exp (((-2 * π * x * -t : ℝ) : ℂ) * Complex.I) =
      Complex.exp (2 * π * Complex.I * t * x) := by
    congr 1
    push_cast
    ring
  simp only [smul_eq_mul]
  rw [he]
  field_simp

/-- The cosine form of the Fourier transform of the Lorentzian. -/
theorem integral_cos_div_sq_add_sq {a : ℂ} (ha : 0 < a.re) (t : ℝ) :
    ∫ x : ℝ, (Real.cos (2 * π * t * x) : ℂ) / ((x : ℂ) ^ 2 + a ^ 2) =
      π / a * Complex.exp (-(2 * π * a) * (|t| : ℝ)) := by
  have h1 := integral_cexp_div_sq_add_sq ha t
  have h2 := integral_cexp_div_sq_add_sq ha (-t)
  have i1 := integrable_cexp_div_sq_add_sq ha t
  have i2 := integrable_cexp_div_sq_add_sq ha (-t)
  have hpt : ∀ x : ℝ, (Real.cos (2 * π * t * x) : ℂ) / ((x : ℂ) ^ 2 + a ^ 2) =
      (Complex.exp (2 * π * Complex.I * t * x) / ((x : ℂ) ^ 2 + a ^ 2) +
        Complex.exp (2 * π * Complex.I * (-t : ℝ) * x) / ((x : ℂ) ^ 2 + a ^ 2)) / 2 := by
    intro x
    rw [Complex.ofReal_cos, Complex.cos]
    have e1 : ((2 * π * t * x : ℝ) : ℂ) * Complex.I = 2 * π * Complex.I * t * x := by
      push_cast
      ring
    have e2 : -((2 * π * t * x : ℝ) : ℂ) * Complex.I = 2 * π * Complex.I * (-t : ℝ) * x := by
      push_cast
      ring
    rw [e1, e2]
    ring
  simp_rw [hpt]
  rw [integral_div, integral_add i1 i2, h1, h2, abs_neg]
  ring

/-! ### The band kernel against the Lorentzian -/

/-- The band kernel is bounded by `2 |Y|`. -/
theorem abs_realBandKernel_le (Y u : ℝ) : |realBandKernel Y u| ≤ 2 * |Y| := by
  rw [realBandKernel, abs_mul, abs_mul, abs_two]
  have := abs_sinc_le_one (2 * π * Y * u)
  nlinarith [abs_nonneg Y]

/-- The band kernel along a ray over the Lorentzian is integrable. -/
theorem integrable_realBandKernel_mul_div_sq_add_sq {a : ℂ} (ha : 0 < a.re) (c Y : ℝ) :
    Integrable fun x : ℝ ↦ (realBandKernel Y (c * x) : ℂ) / ((x : ℂ) ^ 2 + a ^ 2) := by
  refine Integrable.mono' ((integrable_inv_sq_add_sq ha).norm.const_mul (2 * |Y|))
    (Continuous.div (Complex.continuous_ofReal.comp
      ((continuous_realBandKernel Y).comp (by fun_prop))) (by fun_prop)
      (ofReal_sq_add_sq_ne_zero ha)).aestronglyMeasurable
    (ae_of_all _ fun x ↦ ?_)
  rw [norm_div, Complex.norm_real, Real.norm_eq_abs, div_eq_mul_inv, norm_inv]
  exact mul_le_mul_of_nonneg_right (abs_realBandKernel_le Y _) (by positivity)

/-- The integral over a symmetric interval of a function of `|η|`. -/
private theorem integral_comp_abs_symm {F : ℝ → ℂ} (hF : Continuous F) {Y : ℝ} (hY : 0 ≤ Y) :
    ∫ η in (-Y)..Y, F |η| = 2 * ∫ η in (0 : ℝ)..Y, F η := by
  have hc : Continuous fun η : ℝ ↦ F |η| := hF.comp continuous_abs
  have h1 : ∫ η in (-Y)..0, F |η| = ∫ η in (0 : ℝ)..Y, F |η| := by
    have h := intervalIntegral.integral_comp_neg (a := (0 : ℝ)) (b := Y) fun η ↦ F |η|
    simp only [abs_neg, neg_zero] at h
    exact h.symm
  have h2 : ∫ η in (0 : ℝ)..Y, F |η| = ∫ η in (0 : ℝ)..Y, F η := by
    refine intervalIntegral.integral_congr fun η hη ↦ ?_
    rw [uIcc_of_le hY] at hη
    simp only [abs_of_nonneg hη.1]
  rw [← intervalIntegral.integral_add_adjacent_intervals (hc.intervalIntegrable (-Y) 0)
    (hc.intervalIntegrable 0 Y), h1, h2]
  ring

/-- **The band kernel along a ray against the Lorentzian.** For `a` of positive real part,
`c > 0` and `Y ≥ 0`, `∫ S (c x) / (x ^ 2 + a ^ 2) dx = (1 - exp (-2 π a c Y)) / (a ^ 2 c)`. -/
theorem integral_realBandKernel_mul_div_sq_add_sq {a : ℂ} (ha : 0 < a.re) {c Y : ℝ}
    (hc : 0 < c) (hY : 0 ≤ Y) :
    ∫ x : ℝ, (realBandKernel Y (c * x) : ℂ) / ((x : ℂ) ^ 2 + a ^ 2) =
      (1 - Complex.exp (-(2 * π * a) * (c * Y : ℝ))) / (a ^ 2 * c) := by
  have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast pi_ne_zero
  have ha0 : a ≠ 0 := fun h ↦ by simp [h] at ha
  have hc0 : (c : ℂ) ≠ 0 := by exact_mod_cast hc.ne'
  have hpt : ∀ x : ℝ, (realBandKernel Y (c * x) : ℂ) / ((x : ℂ) ^ 2 + a ^ 2) =
      ∫ η in (-Y)..Y, (Real.cos (2 * π * (c * η) * x) : ℂ) / ((x : ℂ) ^ 2 + a ^ 2) := by
    intro x
    rw [intervalIntegral.integral_div, intervalIntegral.integral_ofReal,
      ← integral_cos_eq_realBandKernel]
    congr 2
    refine intervalIntegral.integral_congr fun η _ ↦ ?_
    congr 1
    ring
  simp_rw [hpt]
  have hint : Integrable (Function.uncurry fun (η x : ℝ) ↦
      (Real.cos (2 * π * (c * η) * x) : ℂ) / ((x : ℂ) ^ 2 + a ^ 2))
      ((volume.restrict (uIoc (-Y) Y)).prod volume) := by
    have : IsFiniteMeasure (volume.restrict (uIoc (-Y) Y)) :=
      isFiniteMeasure_restrict.mpr measure_Ioc_lt_top.ne
    have hb : Integrable (fun p : ℝ × ℝ ↦ (1 : ℝ) * ‖((p.2 : ℂ) ^ 2 + a ^ 2)⁻¹‖)
        ((volume.restrict (uIoc (-Y) Y)).prod volume) :=
      Integrable.mul_prod (integrable_const (1 : ℝ)) (integrable_inv_sq_add_sq ha).norm
    refine Integrable.mono' hb ?_ (ae_of_all _ fun p ↦ ?_)
    · refine Continuous.aestronglyMeasurable ?_
      unfold Function.uncurry
      exact Continuous.div (by fun_prop) (by fun_prop)
        fun p ↦ ofReal_sq_add_sq_ne_zero ha p.2
    · simp only [Function.uncurry, one_mul]
      rw [norm_div, Complex.norm_real, Real.norm_eq_abs, norm_inv, div_eq_mul_inv]
      exact mul_le_of_le_one_left (by positivity) (abs_cos_le_one _)
  rw [← intervalIntegral_integral_swap hint]
  have hin : ∀ η : ℝ, ∫ x : ℝ, (Real.cos (2 * π * (c * η) * x) : ℂ) / ((x : ℂ) ^ 2 + a ^ 2) =
      π / a * Complex.exp (-(2 * π * a * c) * (|η| : ℝ)) := by
    intro η
    rw [integral_cos_div_sq_add_sq ha (c * η), abs_mul, abs_of_pos hc]
    congr 2
    push_cast
    ring
  simp_rw [hin]
  have hne : -(2 * π * a * c) ≠ 0 := by
    simp only [ne_eq, neg_eq_zero, mul_eq_zero, OfNat.ofNat_ne_zero, false_or]
    tauto
  rw [intervalIntegral.integral_const_mul,
    integral_comp_abs_symm (F := fun η ↦ Complex.exp (-(2 * π * a * c) * (η : ℝ)))
      (by fun_prop) hY,
    integral_exp_mul_complex hne]
  simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero]
  have he : -(2 * π * a) * ((c * Y : ℝ) : ℂ) = -(2 * π * a * c) * Y := by
    push_cast
    ring
  rw [he]
  field_simp
  ring

/-! ### The limit of the diagonal integral -/

/-- The integral over a symmetric interval of an even continuous real function. -/
private theorem integral_symm_of_even_real {f : ℝ → ℝ} (hf : ∀ x, f (-x) = f x)
    (hc : Continuous f) (L : ℝ) : ∫ x in (-L)..L, f x = 2 * ∫ x in (0 : ℝ)..L, f x := by
  have h1 : ∫ x in (-L)..0, f x = ∫ x in (0 : ℝ)..L, f x := by
    have h := intervalIntegral.integral_comp_neg (a := (0 : ℝ)) (b := L) f
    simp only [hf, neg_zero] at h
    exact h.symm
  rw [← intervalIntegral.integral_add_adjacent_intervals (hc.intervalIntegrable (-L) 0)
    (hc.intervalIntegrable 0 L), h1]
  ring

/-- The integral of the band kernel along a ray over `[-L, L]` tends to `1 / c`. -/
theorem tendsto_integral_realBandKernel_mul_symm {Y c : ℝ} (hY : 0 < Y) (hc : 0 < c) :
    Tendsto (fun L : ℝ ↦ ∫ z in (-L)..L, realBandKernel Y (c * z)) atTop (𝓝 c⁻¹) := by
  have hR : Tendsto (fun L : ℝ ↦ Y * L) atTop atTop := tendsto_id.const_mul_atTop hY
  have h := ((tendsto_integral_sinc_mul_of_pos hR (c := 2 * π * c) (by positivity)).const_mul
    (2 * (π * c)⁻¹))
  have e : 2 * (π * c)⁻¹ * (π / 2) = c⁻¹ := by
    field_simp
  rw [e] at h
  refine h.congr fun L ↦ ?_
  rw [integral_symm_of_even_real (f := fun z ↦ realBandKernel Y (c * z))
    (fun z ↦ by rw [mul_neg, realBandKernel_neg])
    ((continuous_realBandKernel Y).comp (by fun_prop)) L,
    integral_realBandKernel_mul hc.ne' Y L]
  ring

/-- Paper: Theorem 12.4.1.1, pp. 514–519, and the value used on p. 520. **The limit of the
diagonal integral over the odd band.** With `K` the kernel of the odd band and `r_g` the
multiplier of the weighted dilation, `g ^ (-1/2) ∫ z in -L..L, r_g z * K (z / g, z)` tends to
`g ^ (3/2) / (g ^ 2 - 1) - g ^ (-1/2) + weightedBandDefect Y g` as `L → ∞`, for every `Y > 0`
and `g > 1`.
Reconstruction: the weighted model of `Sec4_WeightedBandKernel`, which is not in the paper. -/
theorem tendsto_integral_weightedDilationMultiplier_mul_realOddBandKernel {Y g : ℝ} (hY : 0 < Y)
    (hg : 1 < g) :
    Tendsto (fun L : ℝ ↦ (((√g)⁻¹ : ℝ) : ℂ) *
        ∫ z in (-L)..L, weightedDilationMultiplier g z * (realOddBandKernel Y (z / g) z : ℂ))
      atTop (𝓝 (((g ^ (3 / 2 : ℝ) / (g ^ 2 - 1) - (√g)⁻¹ : ℝ) : ℂ) + weightedBandDefect Y g)) := by
  have hg0 : 0 < g := by linarith
  have hcm0 : 0 < 1 - 1 / g := by
    rw [sub_pos, div_lt_one hg0]
    exact hg
  have hcp0 : 0 < 1 + 1 / g := by positivity
  -- the kernel on the diagonal
  have hK : ∀ z : ℝ, realOddBandKernel Y (z / g) z =
      (realBandKernel Y ((1 - 1 / g) * z) - realBandKernel Y ((1 + 1 / g) * z)) / 2 := by
    intro z
    rw [realOddBandKernel, show z / g - z = -((1 - 1 / g) * z) by ring, realBandKernel_neg,
      show z / g + z = (1 + 1 / g) * z by ring]
  have hKc : Continuous fun z : ℝ ↦ realOddBandKernel Y (z / g) z := by
    unfold realOddBandKernel
    exact (((continuous_realBandKernel Y).comp (by fun_prop)).sub
      ((continuous_realBandKernel Y).comp (by fun_prop))).div_const 2
  have hcont (c : ℝ) : Continuous fun z : ℝ ↦ realBandKernel Y (c * z) :=
    (continuous_realBandKernel Y).comp (by fun_prop)
  -- the constant part of the multiplier
  have h1 : Tendsto (fun L : ℝ ↦ ∫ z in (-L)..L, realOddBandKernel Y (z / g) z) atTop
      (𝓝 (((1 - 1 / g)⁻¹ - (1 + 1 / g)⁻¹) / 2)) := by
    have h := ((tendsto_integral_realBandKernel_mul_symm hY hcm0).sub
      (tendsto_integral_realBandKernel_mul_symm hY hcp0)).div_const 2
    refine h.congr fun L ↦ ?_
    simp_rw [hK]
    rw [intervalIntegral.integral_div, intervalIntegral.integral_sub
      ((hcont _).intervalIntegrable _ _) ((hcont _).intervalIntegrable _ _)]
  -- the rational part of the multiplier
  set a : ℂ := -Complex.I * g * weightedZero with ha_def
  have ha : 0 < a.re := by
    have him := weightedZero_im
    have hsq : 0 < 1 / √2 := by positivity
    simp only [ha_def, Complex.mul_re, Complex.neg_re, Complex.I_re, Complex.neg_im,
      Complex.I_im, Complex.ofReal_re, Complex.ofReal_im, Complex.mul_im, him]
    nlinarith
  have ha2 : a ^ 2 = -Complex.I * (g : ℂ) ^ 2 := by
    rw [ha_def, mul_pow, mul_pow, weightedZero_sq, neg_sq, Complex.I_sq]
    ring
  have hden : ∀ z : ℝ, (z : ℂ) ^ 2 - Complex.I * (g : ℂ) ^ 2 = (z : ℂ) ^ 2 + a ^ 2 := by
    intro z
    rw [ha2]
    ring
  have im (c : ℝ) := integrable_realBandKernel_mul_div_sq_add_sq ha c Y
  have hρpt : ∀ z : ℝ, Complex.I * (g : ℂ) * ((g : ℂ) ^ 2 - 1) /
        ((z : ℂ) ^ 2 - Complex.I * (g : ℂ) ^ 2) * (realOddBandKernel Y (z / g) z : ℂ) =
      Complex.I * (g : ℂ) * ((g : ℂ) ^ 2 - 1) / 2 *
        ((realBandKernel Y ((1 - 1 / g) * z) : ℂ) / ((z : ℂ) ^ 2 + a ^ 2) -
          (realBandKernel Y ((1 + 1 / g) * z) : ℂ) / ((z : ℂ) ^ 2 + a ^ 2)) := by
    intro z
    rw [hK, hden]
    push_cast
    ring
  have hρint : Integrable fun z : ℝ ↦ Complex.I * (g : ℂ) * ((g : ℂ) ^ 2 - 1) /
      ((z : ℂ) ^ 2 - Complex.I * (g : ℂ) ^ 2) * (realOddBandKernel Y (z / g) z : ℂ) := by
    simp_rw [hρpt]
    exact ((im _).sub (im _)).const_mul _
  have h2 := intervalIntegral_tendsto_integral hρint tendsto_neg_atTop_atBot tendsto_id
  have hgc : (g : ℂ) ≠ 0 := by exact_mod_cast hg0.ne'
  have hgm : (g : ℂ) - 1 ≠ 0 := by
    have : g - 1 ≠ 0 := by linarith
    exact_mod_cast this
  have hgp : (g : ℂ) + 1 ≠ 0 := by
    have : g + 1 ≠ 0 := by linarith
    exact_mod_cast this
  have hI : Complex.I ≠ 0 := Complex.I_ne_zero
  have h2v : ∫ z : ℝ, Complex.I * (g : ℂ) * ((g : ℂ) ^ 2 - 1) /
      ((z : ℂ) ^ 2 - Complex.I * (g : ℂ) ^ 2) * (realOddBandKernel Y (z / g) z : ℂ) =
      -1 + (((g : ℂ) + 1) / 2 * Complex.exp (2 * π * Complex.I * Y * (g - 1) * weightedZero) -
        ((g : ℂ) - 1) / 2 * Complex.exp (2 * π * Complex.I * Y * (g + 1) * weightedZero)) := by
    simp_rw [hρpt]
    rw [integral_const_mul, integral_sub (im _) (im _),
      integral_realBandKernel_mul_div_sq_add_sq ha hcm0 hY.le,
      integral_realBandKernel_mul_div_sq_add_sq ha hcp0 hY.le]
    have e1 : -(2 * π * a) * (((1 - 1 / g) * Y : ℝ) : ℂ) =
        2 * π * Complex.I * Y * (g - 1) * weightedZero := by
      rw [ha_def]
      push_cast
      field_simp
    have e2 : -(2 * π * a) * (((1 + 1 / g) * Y : ℝ) : ℂ) =
        2 * π * Complex.I * Y * (g + 1) * weightedZero := by
      rw [ha_def]
      push_cast
      field_simp
    have d1 : a ^ 2 * ((1 - 1 / g : ℝ) : ℂ) = -Complex.I * g * (g - 1) := by
      rw [ha2]
      push_cast
      field_simp
    have d2 : a ^ 2 * ((1 + 1 / g : ℝ) : ℂ) = -Complex.I * g * (g + 1) := by
      rw [ha2]
      push_cast
      field_simp
    rw [e1, e2, d1, d2]
    field_simp
    ring
  -- assemble
  have hsplit : ∀ L : ℝ, ∫ z in (-L)..L,
      weightedDilationMultiplier g z * (realOddBandKernel Y (z / g) z : ℂ) =
      (g : ℂ) * ((∫ z in (-L)..L, realOddBandKernel Y (z / g) z : ℝ) : ℂ) +
        ∫ z in (-L)..L, Complex.I * (g : ℂ) * ((g : ℂ) ^ 2 - 1) /
          ((z : ℂ) ^ 2 - Complex.I * (g : ℂ) ^ 2) * (realOddBandKernel Y (z / g) z : ℂ) := by
    intro L
    have hKcc : Continuous fun z : ℝ ↦ (realOddBandKernel Y (z / g) z : ℂ) :=
      Complex.continuous_ofReal.comp hKc
    have hρc : Continuous fun z : ℝ ↦ Complex.I * (g : ℂ) * ((g : ℂ) ^ 2 - 1) /
        ((z : ℂ) ^ 2 - Complex.I * (g : ℂ) ^ 2) * (realOddBandKernel Y (z / g) z : ℂ) :=
      (Continuous.div (by fun_prop) (by fun_prop)
        (weightedDilationMultiplier_den_ne_zero hg0.ne')).mul hKcc
    rw [← intervalIntegral.integral_ofReal, ← intervalIntegral.integral_const_mul,
      ← intervalIntegral.integral_add ((hKcc.const_mul _).intervalIntegrable _ _)
        (hρc.intervalIntegrable _ _)]
    refine intervalIntegral.integral_congr fun z _ ↦ ?_
    rw [weightedDilationMultiplier_eq hg0.ne']
    ring
  have hlim := ((((Complex.continuous_ofReal.tendsto _).comp h1).const_mul (g : ℂ)).add
    h2).const_mul (((√g)⁻¹ : ℝ) : ℂ)
  have hval : (((√g)⁻¹ : ℝ) : ℂ) * ((g : ℂ) * ((((1 - 1 / g)⁻¹ - (1 + 1 / g)⁻¹) / 2 : ℝ) : ℂ) +
      ∫ z : ℝ, Complex.I * (g : ℂ) * ((g : ℂ) ^ 2 - 1) /
        ((z : ℂ) ^ 2 - Complex.I * (g : ℂ) ^ 2) * (realOddBandKernel Y (z / g) z : ℂ)) =
      ((g ^ (3 / 2 : ℝ) / (g ^ 2 - 1) - (√g)⁻¹ : ℝ) : ℂ) + weightedBandDefect Y g := by
    have hs : 0 < √g := Real.sqrt_pos.mpr hg0
    have hsc : ((√g : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hs.ne'
    have hs2 : ((√g : ℝ) : ℂ) ^ 2 = g := by
      rw [← Complex.ofReal_pow, Real.sq_sqrt hg0.le]
    have h32 : g ^ (3 / 2 : ℝ) = g * √g := by
      rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add hg0, Real.rpow_one,
        Real.sqrt_eq_rpow]
    have hgm' : g - 1 ≠ 0 := by linarith
    have hgp' : g + 1 ≠ 0 := by linarith
    have hfirst : (((1 - 1 / g)⁻¹ - (1 + 1 / g)⁻¹) / 2 : ℝ) = g / (g ^ 2 - 1) := by
      have : g ^ 2 - 1 ≠ 0 := by nlinarith
      field_simp
      ring
    rw [h2v, hfirst, weightedBandDefect, h32]
    have hg21 : (g : ℂ) ^ 2 - 1 ≠ 0 := by
      have : g ^ 2 - 1 ≠ 0 := by nlinarith
      exact_mod_cast this
    push_cast
    rw [← hs2] at hg21 hgm hgp ⊢
    field_simp
    ring
  rw [← hval]
  refine hlim.congr fun L ↦ ?_
  simp only [Function.comp_apply, id_eq]
  rw [hsplit L]

end RiemannMasullo
