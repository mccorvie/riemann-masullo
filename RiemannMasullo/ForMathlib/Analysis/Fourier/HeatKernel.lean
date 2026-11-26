module

public import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.MeasureTheory.Function.L2Space

/-! # Heat-kernel moments and the cosine transform

These are normalized real-variable forms of the Gaussian mass, variance and characteristic
function, used in the jump-measure representation of fractional Sobolev energies.
-/

@[expose] public noncomputable section
open MeasureTheory ProbabilityTheory Set Real
namespace RiemannMasullo

/-- The real heat kernel at time `u`, with variance `2u`. -/
def realHeatKernel (u x : ℝ) : ℝ :=
  gaussianPDFReal 0 (2 * u.toNNReal) x

/-- The heat density is jointly measurable in time and position. -/
@[fun_prop]
theorem measurable_realHeatKernel : Measurable (fun p : ℝ × ℝ ↦ realHeatKernel p.1 p.2) := by
  unfold realHeatKernel
  fun_prop

/-- The heat density is nonnegative. -/
theorem realHeatKernel_nonneg (u x : ℝ) : 0 ≤ realHeatKernel u x :=
  gaussianPDFReal_nonneg _ _ _

/-- At positive time the Gaussian density is the classical real heat kernel. -/
theorem realHeatKernel_eq {u : ℝ} (hu : 0 < u) (x : ℝ) :
    realHeatKernel u x = (Real.sqrt (4 * Real.pi * u))⁻¹ *
      Real.exp (-(x ^ 2 / (4 * u))) := by
  simp only [realHeatKernel, gaussianPDFReal, NNReal.coe_mul, NNReal.coe_ofNat,
    Real.coe_toNNReal u hu.le, sub_zero]
  congr 2 <;> ring_nf

private theorem heatVariance_ne_zero {u : ℝ} (hu : 0 < u) :
    2 * u.toNNReal ≠ 0 := by
  have : 0 < u.toNNReal := Real.toNNReal_pos.mpr hu
  positivity

/-- The heat density is integrable at every time. -/
theorem integrable_realHeatKernel (u : ℝ) : Integrable (realHeatKernel u) :=
  integrable_gaussianPDFReal _ _

/-- At positive time the heat kernel has total mass one. -/
theorem integral_realHeatKernel {u : ℝ} (hu : 0 < u) :
    (∫ x : ℝ, realHeatKernel u x) = 1 :=
  integral_gaussianPDFReal_eq_one _ (heatVariance_ne_zero hu)

/-- The positive-time heat kernel has an integrable second moment. -/
theorem integrable_realHeatKernel_mul_sq {u : ℝ} (hu : 0 < u) :
    Integrable (fun x : ℝ ↦ realHeatKernel u x * x ^ 2) := by
  have hi : Integrable (fun x : ℝ ↦ x ^ 2) (gaussianReal 0 (2 * u.toNNReal)) :=
    (memLp_id_gaussianReal' 2 (by norm_num)).integrable_sq
  rw [gaussianReal_of_var_ne_zero _ (heatVariance_ne_zero hu)] at hi
  rw [integrable_withDensity_iff (measurable_gaussianPDF _ _)
    (.of_forall fun _ ↦ gaussianPDF_lt_top)] at hi
  simpa only [gaussianPDF_def, ENNReal.toReal_ofReal (gaussianPDFReal_nonneg _ _ _),
    mul_comm, realHeatKernel] using hi

/-- The second moment of the heat kernel at time `u` is `2u`. -/
theorem integral_realHeatKernel_mul_sq {u : ℝ} (hu : 0 < u) :
    (∫ x : ℝ, realHeatKernel u x * x ^ 2) = 2 * u := by
  have hv := variance_fun_id_gaussianReal (μ := 0) (v := 2 * u.toNNReal)
  rw [variance_eq_integral measurable_id'.aemeasurable, integral_id_gaussianReal] at hv
  simp only [sub_zero] at hv
  rw [integral_gaussianReal_eq_integral_smul (heatVariance_ne_zero hu)] at hv
  simpa only [smul_eq_mul, NNReal.coe_mul, NNReal.coe_ofNat, Real.coe_toNNReal u hu.le,
    realHeatKernel] using hv


/-- The cosine transform of the heat kernel is integrable. -/
theorem integrable_realHeatKernel_mul_cos (u ξ : ℝ) :
    Integrable (fun x : ℝ ↦ realHeatKernel u x * Real.cos (ξ * x)) := by
  apply (integrable_realHeatKernel u).mono' (by unfold realHeatKernel; fun_prop)
  exact .of_forall fun x ↦ by
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (realHeatKernel_nonneg _ _)]
    exact mul_le_of_le_one_right (realHeatKernel_nonneg _ _) (Real.abs_cos_le_one _)

/-- The cosine transform of the heat kernel is the Gaussian Fourier multiplier. -/
theorem integral_realHeatKernel_mul_cos {u : ℝ} (hu : 0 < u) (ξ : ℝ) :
    (∫ x : ℝ, realHeatKernel u x * Real.cos (ξ * x)) = Real.exp (-(u * ξ ^ 2)) := by
  have h := charFun_gaussianReal (μ := 0) (v := 2 * u.toNNReal) ξ
  rw [charFun_apply_real, integral_gaussianReal_eq_integral_smul (heatVariance_ne_zero hu)] at h
  have hi : Integrable (fun x : ℝ ↦ (realHeatKernel u x : ℂ) *
      Complex.exp (((ξ * x : ℝ) : ℂ) * Complex.I)) := by
    apply (integrable_realHeatKernel u).mono' (by unfold realHeatKernel; fun_prop)
    exact .of_forall fun x ↦ by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (realHeatKernel_nonneg _ _), Complex.norm_exp]
      simp
  have he : Complex.exp ((ξ : ℂ) * 0 * Complex.I -
      (((2 * u.toNNReal : NNReal) : ℝ) : ℂ) * (ξ : ℂ) ^ 2 / 2) =
      (Real.exp (-(u * ξ ^ 2)) : ℂ) := by
    rw [Complex.ofReal_exp]
    congr 1
    rw [NNReal.coe_mul, NNReal.coe_ofNat, Real.coe_toNNReal u hu.le]
    push_cast
    ring
  simp only [Complex.ofReal_zero, Complex.real_smul, ← Complex.ofReal_mul] at h
  rw [he] at h
  have hr := congrArg Complex.re h
  have hre := Complex.reCLM.integral_comp_comm hi
  change (∫ x : ℝ, ((realHeatKernel u x : ℂ) * Complex.exp (((ξ * x : ℝ) : ℂ) * Complex.I)).re) =
    (∫ x : ℝ, (realHeatKernel u x : ℂ) * Complex.exp (((ξ * x : ℝ) : ℂ) * Complex.I)).re at hre
  simp only [realHeatKernel] at hre
  rw [← hre] at hr
  simpa only [Complex.real_smul, realHeatKernel, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero, ← Complex.ofReal_mul,
    Complex.exp_ofReal_mul_I_re] using hr

/-- The heat-kernel contribution to a jump symbol is integrable. -/
theorem integrable_realHeatKernel_mul_one_sub_cos (u ξ : ℝ) :
    Integrable (fun x : ℝ ↦ realHeatKernel u x * (1 - Real.cos (ξ * x))) := by
  simpa only [mul_sub, mul_one, Pi.sub_def] using
    (integrable_realHeatKernel u).sub (integrable_realHeatKernel_mul_cos u ξ)

/-- The heat-kernel jump symbol is one minus its Gaussian Fourier multiplier. -/
theorem integral_realHeatKernel_mul_one_sub_cos {u : ℝ} (hu : 0 < u) (ξ : ℝ) :
    (∫ x : ℝ, realHeatKernel u x * (1 - Real.cos (ξ * x))) =
      1 - Real.exp (-(u * ξ ^ 2)) := by
  simp_rw [mul_sub, mul_one]
  rw [integral_sub (integrable_realHeatKernel u) (integrable_realHeatKernel_mul_cos u ξ),
    integral_realHeatKernel hu, integral_realHeatKernel_mul_cos hu]

end RiemannMasullo
