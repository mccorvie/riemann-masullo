module

public import RiemannMasullo.ForMathlib.MeasureTheory.Integral.PoissonLogQuadrature
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Tactic

/-! # Global domination and height tails of the reference Cauchy measure -/

@[expose] public noncomputable section

open MeasureTheory Set ProbabilityTheory
open scoped ENNReal

namespace RiemannMasullo.LogQuadrature

/-- The density at the reference point two is bounded by its value at zero. -/
theorem poissonMeasure_le_smul_volume :
    poissonMeasure ≤ ENNReal.ofReal (2/(3*Real.pi)) • (volume : Measure ℝ) := by
  rw [poissonMeasure,cauchyMeasure_of_scale_ne_zero _ (by norm_num),← withDensity_const]
  apply withDensity_mono
  filter_upwards with x
  rw [cauchyPDF]
  apply ENNReal.ofReal_le_ofReal
  rw [cauchyPDFReal_def']
  norm_num only [NNReal.coe_div,NNReal.coe_ofNat,sub_zero]
  have h : (1+(x/(3/2))^2)⁻¹ ≤ 1 := (inv_le_one₀ (by positivity)).mpr (by nlinarith [sq_nonneg (x/(3/2))])
  calc Real.pi⁻¹ * (2/3:ℝ) * (1+(x/(3/2))^2)⁻¹ ≤ Real.pi⁻¹ * (2/3:ℝ) * 1 :=
        mul_le_mul_of_nonneg_left h (by positivity)
    _ = 2/(3*Real.pi) := by ring

/-- Every set, including a nonmeasurable set, obeys the same domination. -/
theorem poissonMeasure_apply_le_volume (E : Set ℝ) :
    poissonMeasure E ≤ ENNReal.ofReal (2/(3*Real.pi)) * volume E := by
  have h := poissonMeasure_le_smul_volume E
  simpa only [smul_apply,smul_eq_mul] using h

/-- The two height tails are bounded by three over pi times the cutoff. -/
theorem poissonMeasure_abs_gt_le {R : ℝ} (hR : 0 < R) :
    poissonMeasure {t | R < |t|} ≤ ENNReal.ofReal ((3/Real.pi)/R) := by
  rw [← ofReal_measureReal (μ:=poissonMeasure) (s:={t | R < |t|})]
  apply ENNReal.ofReal_le_ofReal
  have hs : {t : ℝ | R < |t|} ⊆ (Ico (-R) R)ᶜ := by
    intro t ht hneg
    exact (not_lt_of_ge (abs_le.mpr ⟨hneg.1,hneg.2.le⟩)) ht
  apply (measureReal_mono (μ:=poissonMeasure) hs).trans
  rw [probReal_compl_eq_one_sub measurableSet_Ico,poisson_Ico (by linarith),
    neg_div,Real.arctan_neg]
  have hr : 0 < R/(3/2) := by positivity
  have ha := Real.arctan_le_self (inv_pos.mpr hr).le
  rw [Real.arctan_inv_of_pos hr] at ha
  calc 1-(Real.arctan (R/(3/2)) - -Real.arctan (R/(3/2)))/Real.pi =
        (2/Real.pi)*(Real.pi/2-Real.arctan (R/(3/2))) := by field_simp; ring
    _ ≤ (2/Real.pi)*(R/(3/2))⁻¹ := mul_le_mul_of_nonneg_left ha (by positivity)
    _ = (3/Real.pi)/R := by field_simp

/-- Outside height two to the n, the Cauchy mass is at most (3/pi) times two to the minus n. -/
theorem poissonMeasure_abs_gt_two_pow (n : ℕ) :
    poissonMeasure {t : ℝ | (2:ℝ)^n < |t|} ≤ ENNReal.ofReal ((3/Real.pi)*(1/2:ℝ)^n) := by
  rw [one_div,inv_pow,←div_eq_mul_inv]
  exact poissonMeasure_abs_gt_le (by positivity)

end RiemannMasullo.LogQuadrature
