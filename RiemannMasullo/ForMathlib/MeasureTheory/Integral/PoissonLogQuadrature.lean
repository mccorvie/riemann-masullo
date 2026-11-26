module

public import RiemannMasullo.ForMathlib.MeasureTheory.Integral.ClippedLogQuadrature
public import Mathlib.Probability.Distributions.Cauchy
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic

/-! # Arctangent cell weights at the reference point two

The Cauchy measure of scale `3/2` has finite logarithmic moment, and each
quadrature cell has an explicit positive arctangent weight. -/

@[expose] public noncomputable section
open Filter MeasureTheory Set ProbabilityTheory
open scoped Topology NNReal ENNReal

namespace RiemannMasullo.LogQuadrature

/-- Harmonic measure on the boundary `Re s = 1/2` viewed from the real point two. -/
abbrev poissonMeasure : Measure ℝ := cauchyMeasure 0 (3/2)

/-- The Cauchy density of scale `3/2` with respect to Lebesgue measure. -/
def poissonWeight (x : ℝ) : ℝ := (3/2) / (Real.pi * ((3/2)^2 + x^2))

private theorem density_eq (x : ℝ) : cauchyPDFReal 0 (3/2) x = poissonWeight x := by
  simp only [cauchyPDFReal,poissonWeight,sub_zero]
  norm_num
  rw [add_comm (x^2)]
  field_simp

private theorem continuous_weight : Continuous poissonWeight := by
  unfold poissonWeight
  exact continuous_const.div (continuous_const.mul (continuous_const.add (continuous_id.pow 2)))
    (fun x : ℝ ↦ by positivity)

private theorem realPDF (x : ℝ) : (cauchyPDF 0 (3/2) x).toReal = poissonWeight x := by
  rw [cauchyPDF, ENNReal.toReal_ofReal (cauchyPDF_pos _ (by norm_num) _).le, density_eq]

theorem poisson_integral (g : ℝ → ℝ) :
    (∫ x, g x ∂poissonMeasure) = ∫ x, poissonWeight x * g x := by
  rw [poissonMeasure,cauchyMeasure_of_scale_ne_zero _ (by norm_num),
    integral_withDensity_eq_integral_toReal_smul (measurable_cauchyPDF _ _) (by simp [cauchyPDF])]
  apply integral_congr_ae
  filter_upwards with x
  rw [cauchyPDF, ENNReal.toReal_ofReal (cauchyPDF_pos _ (by norm_num) _).le,
    smul_eq_mul, density_eq]

theorem poisson_integrable_iff (g : ℝ → ℝ) :
    Integrable g poissonMeasure ↔ Integrable (fun x ↦ poissonWeight x * g x) := by
  rw [poissonMeasure,cauchyMeasure_of_scale_ne_zero _ (by norm_num),
    integrable_withDensity_iff_integrable_smul' (measurable_cauchyPDF _ _) (by simp [cauchyPDF])]
  simp only [realPDF,smul_eq_mul]

theorem poisson_logMoment : Integrable (fun x : ℝ ↦ Real.log (2+|x|)) poissonMeasure := by
  rw [poisson_integrable_iff]
  have hI := integrable_one_add_norm (E:=ℝ) (μ:=volume) (r:=3/2) (by norm_num)
  have hc : Continuous (fun x : ℝ ↦ Real.log (2+|x|)) :=
    (continuous_const.add continuous_abs).log (fun x : ℝ ↦ by change (2:ℝ)+|x| ≠ 0; positivity)
  apply (hI.const_mul (12/Real.pi)).mono' (continuous_weight.mul hc).aestronglyMeasurable
  filter_upwards with x
  have hpos : 0 < 1+|x| := by positivity
  have hpos' : 0 < 2+|x| := by positivity
  have hl : 0 ≤ Real.log (2+|x|) := Real.log_nonneg (by linarith [abs_nonneg x])
  have hp : 0 < poissonWeight x := by unfold poissonWeight; positivity
  change ‖poissonWeight x * Real.log (2+|x|)‖ ≤ _
  rw [Real.norm_of_nonneg (mul_nonneg hp.le hl),Real.norm_eq_abs]
  have hweight : poissonWeight x ≤ (3/Real.pi)/(1+|x|)^2 := by
    unfold poissonWeight
    have hd : (1+|x|)^2 ≤ 2*((3/2:ℝ)^2+x^2) := by nlinarith [sq_nonneg (|x|-1),sq_abs x]
    calc (3/2:ℝ)/(Real.pi*((3/2)^2+x^2)) = (3/Real.pi)/(2*((3/2)^2+x^2)) := by
          rw [div_div,div_div]; congr 1; ring
      _ ≤ _ := div_le_div_of_nonneg_left (by positivity) (by positivity) hd
  have hlog : Real.log (2+|x|) ≤ 4*(1+|x|)^(1/2:ℝ) := by
    have hs := Real.sqrt_pos.mpr hpos'
    have h₁ := Real.log_le_sub_one_of_pos hs
    rw [Real.log_sqrt hpos'.le] at h₁
    have h₂ : Real.sqrt (2+|x|) ≤ 2 * Real.sqrt (1+|x|) := by
      nlinarith [Real.sq_sqrt hpos'.le,Real.sq_sqrt hpos.le,
        Real.sqrt_nonneg (2+|x|),Real.sqrt_nonneg (1+|x|),abs_nonneg x]
    rw [← Real.sqrt_eq_rpow]
    linarith
  calc poissonWeight x * Real.log (2+|x|) ≤
      ((3/Real.pi)/(1+|x|)^2)*(4*(1+|x|)^(1/2:ℝ)) :=
        mul_le_mul hweight hlog hl (by positivity)
    _ = (12/Real.pi)*(1+|x|)^(-(3/2):ℝ) := by
      rw [show (-(3/2):ℝ) = -2+(1/2) by ring,Real.rpow_add hpos, Real.rpow_neg hpos.le]
      norm_num
      ring

/-- Each interval mass is an elementary arctangent difference. -/
theorem poisson_Ico {a b : ℝ} (hab : a ≤ b) :
    poissonMeasure.real (Ico a b) = (Real.arctan (b/(3/2)) - Real.arctan (a/(3/2)))/Real.pi := by
  have he : poissonMeasure.real (Ico a b) = ∫ x in Ico a b, poissonWeight x := by
    rw [Measure.real,poissonMeasure,cauchyMeasure_of_scale_ne_zero _ (by norm_num),
      MeasureTheory.withDensity_apply _ measurableSet_Ico]
    simp only [cauchyPDF,density_eq]
    exact (integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun x ↦ by
      change 0 ≤ poissonWeight x; unfold poissonWeight; positivity)
      (continuous_weight.aestronglyMeasurable)).symm
  rw [he,integral_Ico_eq_integral_Ioc,← intervalIntegral.integral_of_le hab]
  have hd (x : ℝ) : HasDerivAt (fun y : ℝ ↦ Real.arctan (y/(3/2))/Real.pi) (poissonWeight x) x := by
    convert ((Real.hasDerivAt_arctan (x/(3/2))).comp x ((hasDerivAt_id x).div_const (3/2))).div_const Real.pi using 1 <;> try rfl
    unfold poissonWeight
    field_simp
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ ↦ hd x)
    (continuous_weight.intervalIntegrable _ _)]
  ring

theorem poisson_cell_pos {n : ℕ} (hn : 0 < n) (j : ℕ) : 0 < poissonMeasure.real (cell n j) := by
  have hh : node n j < node n (j+1) := by rw [node_dist]; linarith [show (0:ℝ)<(n:ℝ)⁻¹ by positivity]
  rw [cell,poisson_Ico hh.le]
  apply div_pos _ Real.pi_pos
  apply sub_pos.mpr
  exact Real.arctan_strictMono (div_lt_div_of_pos_right hh (by norm_num))


/-- The Cauchy measure at two has a finite square-root height moment. -/
theorem poisson_sqrtMoment : Integrable (fun x : ℝ ↦ Real.sqrt (1+|x|)) poissonMeasure := by
  rw [poisson_integrable_iff]
  have hi := integrable_one_add_norm (E:=ℝ) (μ:=volume) (r:=3/2) (by norm_num)
  have hc : Continuous (fun x : ℝ ↦ Real.sqrt (1+|x|)) :=
    Real.continuous_sqrt.comp (continuous_const.add continuous_abs)
  apply (hi.const_mul (3/Real.pi)).mono' (continuous_weight.mul hc).aestronglyMeasurable
  filter_upwards with x
  have hpos : 0 < 1+|x| := by positivity
  have hw : 0 < poissonWeight x := by unfold poissonWeight; positivity
  have hweight : poissonWeight x ≤ (3/Real.pi)/(1+|x|)^2 := by
    unfold poissonWeight
    have hd : (1+|x|)^2 ≤ 2*((3/2:ℝ)^2+x^2) := by nlinarith [sq_nonneg (|x|-1),sq_abs x]
    calc (3/2:ℝ)/(Real.pi*((3/2)^2+x^2)) = (3/Real.pi)/(2*((3/2)^2+x^2)) := by
          rw [div_div,div_div]; congr 1; ring
      _ ≤ _ := div_le_div_of_nonneg_left (by positivity) (by positivity) hd
  change ‖poissonWeight x * Real.sqrt (1+|x|)‖ ≤ (3/Real.pi)*(1+‖x‖)^(-(3/2):ℝ)
  rw [Real.norm_of_nonneg (mul_nonneg hw.le (Real.sqrt_nonneg _)),Real.norm_eq_abs]
  calc
    poissonWeight x * Real.sqrt (1+|x|) ≤ ((3/Real.pi)/(1+|x|)^2) * Real.sqrt (1+|x|) :=
      mul_le_mul_of_nonneg_right hweight (Real.sqrt_nonneg _)
    _ = _ := by
      rw [Real.sqrt_eq_rpow,show -(3/2:ℝ) = -2 + 1/2 by ring,
        Real.rpow_add hpos,Real.rpow_neg hpos.le]
      norm_num
      ring

end RiemannMasullo.LogQuadrature
