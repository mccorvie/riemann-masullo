module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
public import Mathlib.MeasureTheory.Integral.CircleAverage
public import Mathlib.Probability.Distributions.Cauchy
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Cotangent
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! # The Cayley boundary parametrization and the Cauchy measure -/

@[expose] public noncomputable section

open Set Real Complex MeasureTheory
open scoped ENNReal NNReal

namespace RiemannMasullo.CayleyCauchy

/-- The ordinate of the image of the angle `θ` at positive scale `a`. -/
def ordinate (a θ : ℝ) : ℝ := a * Real.tan ((π - θ) / 2)

/-- The inverse parametrization takes the whole real line onto the punctured circle's
angular interval in decreasing order. -/
def inverseAngle (a t : ℝ) : ℝ := π - 2 * Real.arctan (t / a)

/-- The centered Cauchy density with scale `a`. -/
def density (a t : ℝ) : ℝ := a / (π * (a ^ 2 + t ^ 2))

theorem inverseAngle_mem (a t : ℝ) : inverseAngle a t ∈ Ioo 0 (2 * π) := by
  unfold inverseAngle
  exact ⟨by linarith [Real.arctan_lt_pi_div_two (t / a)],
    by linarith [Real.neg_pi_div_two_lt_arctan (t / a)]⟩

theorem ordinate_inverseAngle {a : ℝ} (ha : 0 < a) (t : ℝ) :
    ordinate a (inverseAngle a t) = t := by
  unfold ordinate inverseAngle
  rw [show (π - (π - 2 * Real.arctan (t / a))) / 2 = Real.arctan (t / a) by ring,
    Real.tan_arctan]
  field_simp

theorem inverseAngle_ordinate {a θ : ℝ} (ha : 0 < a) (hθ : θ ∈ Ioo 0 (2 * π)) :
    inverseAngle a (ordinate a θ) = θ := by
  unfold inverseAngle ordinate
  rw [mul_div_cancel_left₀ _ ha.ne', Real.arctan_tan (by linarith [hθ.2]) (by linarith [hθ.1])]
  ring

theorem range_inverseAngle {a : ℝ} (ha : 0 < a) :
    range (inverseAngle a) = Ioo 0 (2 * π) :=
  Subset.antisymm (range_subset_iff.mpr (inverseAngle_mem a))
    (fun θ hθ ↦ ⟨ordinate a θ, inverseAngle_ordinate ha hθ⟩)

theorem hasDerivAt_inverseAngle {a : ℝ} (ha : 0 < a) (t : ℝ) :
    HasDerivAt (inverseAngle a) (-(2 * a / (a ^ 2 + t ^ 2))) t := by
  have h := ((((hasDerivAt_id' t).div_const a).arctan).const_mul 2).const_sub π
  unfold inverseAngle
  convert h using 1
  have h₁ : a ^ 2 + t ^ 2 ≠ 0 := by positivity
  have h₂ : 1 + (t / a) ^ 2 ≠ 0 := by positivity
  field_simp [div_pow]

private theorem abs_jacobian {a : ℝ} (ha : 0 < a) (t : ℝ) :
    |-(2 * a / (a ^ 2 + t ^ 2))| = (2 * π) * density a t := by
  rw [abs_neg, abs_of_nonneg (by positivity), density]
  field_simp

private theorem image_integral {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {a : ℝ} (ha : 0 < a) (G : ℝ → E) :
    ∫ θ in Ioo 0 (2 * π), G θ =
      (2 * π) • ∫ t, density a t • G (inverseAngle a t) := by
  have h := integral_image_eq_integral_abs_deriv_smul (s := (univ : Set ℝ))
    MeasurableSet.univ (fun t _ ↦ (hasDerivAt_inverseAngle ha t).hasDerivWithinAt)
    (Function.LeftInverse.injective (ordinate_inverseAngle ha)).injOn G
  rw [image_univ, range_inverseAngle ha, setIntegral_univ] at h
  rw [h, ← integral_smul]
  apply integral_congr_ae
  filter_upwards with t
  rw [abs_jacobian ha, smul_smul]

/-- Normalized substitution in the angular integral, valid for arbitrary Bochner tests. -/
theorem integral_angle {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {a : ℝ} (ha : 0 < a) (G : ℝ → E) :
    (2 * π)⁻¹ • ∫ θ in Ioo 0 (2 * π), G θ =
      ∫ t, density a t • G (inverseAngle a t) := by
  rw [image_integral ha, inv_smul_smul₀ (by positivity)]

/-- Absolute integrability in angle is equivalent to integrability with the Cauchy density. -/
theorem integrableOn_angle_iff {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {a : ℝ} (ha : 0 < a) (G : ℝ → E) :
    IntegrableOn G (Ioo 0 (2 * π)) ↔
      Integrable (fun t ↦ density a t • G (inverseAngle a t)) := by
  have h := integrableOn_image_iff_integrableOn_abs_deriv_smul (s := (univ : Set ℝ))
    MeasurableSet.univ (fun t _ ↦ (hasDerivAt_inverseAngle ha t).hasDerivWithinAt)
    (Function.LeftInverse.injective (ordinate_inverseAngle ha)).injOn G
  rw [image_univ, range_inverseAngle ha, integrableOn_univ] at h
  have he (t : ℝ) : |-(2 * a / (a ^ 2 + t ^ 2))| • G (inverseAngle a t) =
      (2 * π) • (density a t • G (inverseAngle a t)) := by rw [abs_jacobian ha, smul_smul]
  simpa only [he, integrable_fun_smul_iff (show 2 * π ≠ 0 by positivity)] using h

/-- Extended nonnegative substitution also applies when either side is infinite. -/
theorem lintegral_angle {a : ℝ} (ha : 0 < a) (G : ℝ → ℝ≥0∞) :
    ENNReal.ofReal (2 * π)⁻¹ * ∫⁻ θ in Ioo 0 (2 * π), G θ =
      ∫⁻ t, ENNReal.ofReal (density a t) * G (inverseAngle a t) := by
  have h := lintegral_image_eq_lintegral_abs_deriv_mul (s := (univ : Set ℝ))
    MeasurableSet.univ (fun t _ ↦ (hasDerivAt_inverseAngle ha t).hasDerivWithinAt)
    (Function.LeftInverse.injective (ordinate_inverseAngle ha)).injOn G
  rw [image_univ, range_inverseAngle ha, setLIntegral_univ] at h
  rw [h]
  simp_rw [abs_jacobian ha, ENNReal.ofReal_mul (show 0 ≤ 2 * π by positivity), mul_assoc]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, ← mul_assoc,
    ← ENNReal.ofReal_mul (show 0 ≤ (2 * π)⁻¹ by positivity),
    inv_mul_cancel₀ (by positivity : 2 * π ≠ 0), ENNReal.ofReal_one, one_mul]

/-- The complex affine Cayley chart on the disk. -/
def chart (b a : ℝ) (z : ℂ) : ℂ := b + a * ((1 + z) / (1 - z))

/-- On the unit circle the chart lies on the vertical line of real part `b`. -/
theorem chart_circleMap (b a θ : ℝ) :
    chart b a (circleMap 0 1 θ) = (b : ℂ) + (ordinate a θ : ℂ) * I := by
  have hcot : Real.cot (θ / 2) = Real.tan ((π - θ) / 2) := by
    rw [show (π - θ) / 2 = π / 2 - θ / 2 by ring, Real.tan_pi_div_two_sub, Real.tan_inv_eq_cot]
  have hc : (1 + Complex.exp ((θ : ℂ) * I)) / (1 - Complex.exp ((θ : ℂ) * I)) =
      (Real.cot (θ / 2) : ℂ) * I := by
    rw [Complex.ofReal_cot, Complex.cot_eq_exp_ratio, Complex.ofReal_div, Complex.ofReal_ofNat,
      show 2 * I * ((θ : ℂ) / 2) = θ * I by ring,
      add_comm (Complex.exp _), mul_comm I, ← div_div, div_mul_cancel₀ _ Complex.I_ne_zero]
  simp only [chart, circleMap_zero, Complex.ofReal_one, one_mul, hc, hcot, ordinate, Complex.ofReal_mul]
  ring

/-- The inverse coordinate sends parameter `t` to the true boundary value `b + it`. -/
theorem chart_inverseAngle (b : ℝ) {a : ℝ} (ha : 0 < a) (t : ℝ) :
    chart b a (circleMap 0 1 (inverseAngle a t)) = (b : ℂ) + t * I := by
  rw [chart_circleMap, ordinate_inverseAngle ha]

/-- Integrating any function of the ordinate against uniform angle gives the
whole-line integral against the centered Cauchy density. -/
theorem integral_ordinate {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {a : ℝ} (ha : 0 < a) (F : ℝ → E) :
    (2 * π)⁻¹ • ∫ θ in Ioo 0 (2 * π), F (ordinate a θ) =
      ∫ t, density a t • F t := by
  simpa only [ordinate_inverseAngle ha] using integral_angle ha (fun θ ↦ F (ordinate a θ))

theorem integrableOn_ordinate_iff {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {a : ℝ} (ha : 0 < a) (F : ℝ → E) :
    IntegrableOn (fun θ ↦ F (ordinate a θ)) (Ioo 0 (2 * π)) ↔
      Integrable (fun t ↦ density a t • F t) := by
  simpa only [ordinate_inverseAngle ha] using integrableOn_angle_iff ha (fun θ ↦ F (ordinate a θ))

/-- Extended nonnegative test functions, including integrals of value infinity. -/
theorem lintegral_ordinate {a : ℝ} (ha : 0 < a) (F : ℝ → ℝ≥0∞) :
    ENNReal.ofReal (2 * π)⁻¹ * ∫⁻ θ in Ioo 0 (2 * π), F (ordinate a θ) =
      ∫⁻ t, ENNReal.ofReal (density a t) * F t := by
  simpa only [ordinate_inverseAngle ha] using lintegral_angle ha (fun θ ↦ F (ordinate a θ))

/-- A circle average written in the inverse-angle coordinate. -/
theorem circleAverage_inverseAngle {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {a : ℝ} (ha : 0 < a) (G : ℂ → E) :
    Real.circleAverage G 0 1 =
      ∫ t, density a t • G (circleMap 0 1 (inverseAngle a t)) := by
  rw [Real.circleAverage_def, intervalIntegral.integral_of_le (by positivity), integral_Ioc_eq_integral_Ioo]
  exact integral_angle ha (fun θ ↦ G (circleMap 0 1 θ))

theorem circleIntegrable_inverseAngle_iff {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {a : ℝ} (ha : 0 < a) (G : ℂ → E) :
    CircleIntegrable G 0 1 ↔
      Integrable (fun t ↦ density a t • G (circleMap 0 1 (inverseAngle a t))) := by
  rw [circleIntegrable_def, intervalIntegrable_iff_integrableOn_Ioc_of_le (by positivity)]
  exact (integrableOn_congr_set_ae Ioo_ae_eq_Ioc.symm).trans
    (integrableOn_angle_iff ha (fun θ ↦ G (circleMap 0 1 θ)))

/-- Boundary values of the shifted Cayley chart averaged on the unit circle. -/
theorem circleAverage_chart {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (b : ℝ) {a : ℝ} (ha : 0 < a) (F : ℂ → E) :
    Real.circleAverage (fun z ↦ F (chart b a z)) 0 1 =
      ∫ t, density a t • F ((b : ℂ) + t * I) := by
  simpa only [chart_inverseAngle b ha] using circleAverage_inverseAngle ha (fun z ↦ F (chart b a z))

theorem circleIntegrable_chart_iff {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (b : ℝ) {a : ℝ} (ha : 0 < a) (F : ℂ → E) :
    CircleIntegrable (fun z ↦ F (chart b a z)) 0 1 ↔
      Integrable (fun t ↦ density a t • F ((b : ℂ) + t * I)) := by
  simpa only [chart_inverseAngle b ha] using circleIntegrable_inverseAngle_iff ha (fun z ↦ F (chart b a z))

private theorem circleMap_ne_one {θ : ℝ} (hθ : θ ∈ Ioo 0 (2 * π)) :
    circleMap 0 1 θ ≠ 1 := by
  intro h
  apply hθ.1.ne'
  apply eq_of_circleMap_eq (c := (0 : ℂ)) (R := (1 : ℝ)) one_ne_zero
    (by simpa only [sub_zero, abs_of_pos hθ.1] using hθ.2)
  simpa [circleMap] using h

private theorem two_add_div_one_sub_eq_chart {z : ℂ} (hz : z ≠ 1) :
    (2 + z) / (1 - z) = chart (1/2) (3/2) z := by
  have hn : 1 - z ≠ 0 := sub_ne_zero.mpr hz.symm
  unfold chart
  push_cast
  field_simp
  ring

/-- The unsplit rational function agrees with the half-plane chart at every finite ordinate. -/
theorem two_add_div_one_sub_inverseAngle (t : ℝ) :
    let z := circleMap 0 1 (inverseAngle (3/2) t)
    (2 + z) / (1 - z) = (1/2 : ℂ) + t * I := by
  let z := circleMap 0 1 (inverseAngle (3/2) t)
  have h := chart_inverseAngle (1/2) (by norm_num : (0 : ℝ) < 3/2) t
  change (2 + z) / (1 - z) = (1/2 : ℂ) + t * I
  calc (2 + z) / (1 - z) = chart (1/2) (3/2) z :=
         two_add_div_one_sub_eq_chart (circleMap_ne_one (inverseAngle_mem (3/2) t))
       _ = _ := by simpa only [Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat] using h

/-- The actual rational function `(2 + z) / (1 - z)` sends the normalized angular
average to the vertical line of real part one half with Cauchy scale three halves. -/
theorem circleAverage_two_add_div_one_sub {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F : ℂ → E) :
    Real.circleAverage (fun z ↦ F ((2 + z) / (1 - z))) 0 1 =
      ∫ t : ℝ, ((3/2) / (π * ((3/2)^2 + t^2))) • F ((1/2 : ℂ) + t * I) := by
  simpa only [two_add_div_one_sub_inverseAngle, density] using
    circleAverage_inverseAngle (by norm_num : (0 : ℝ) < 3/2) (fun z ↦ F ((2 + z) / (1 - z)))

theorem circleIntegrable_two_add_div_one_sub_iff {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F : ℂ → E) :
    CircleIntegrable (fun z ↦ F ((2 + z) / (1 - z))) 0 1 ↔
      Integrable (fun t : ℝ ↦ ((3/2) / (π * ((3/2)^2 + t^2))) • F ((1/2 : ℂ) + t * I)) := by
  simpa only [two_add_div_one_sub_inverseAngle, density] using
    circleIntegrable_inverseAngle_iff (by norm_num : (0 : ℝ) < 3/2) (fun z ↦ F ((2 + z) / (1 - z)))

/-- Uniform angular probability, with the omitted endpoint having zero mass. -/
def uniformAngle : Measure ℝ :=
  ENNReal.ofReal (2 * π)⁻¹ • volume.restrict (Ioo 0 (2 * π))

theorem cauchyPDFReal_zero (a : ℝ≥0) (t : ℝ) :
    ProbabilityTheory.cauchyPDFReal 0 a t = density a t := by
  rw [ProbabilityTheory.cauchyPDFReal, density, sub_zero, add_comm (t ^ 2), div_eq_mul_inv, mul_inv_rev]
  ring

theorem measurable_ordinate (a : ℝ) : Measurable (ordinate a) := by
  change Measurable (fun θ : ℝ ↦ a * Real.tan ((π - θ) / 2))
  simp_rw [Real.tan_eq_sin_div_cos]
  fun_prop

/-- The pushforward of uniform angle is Mathlib's centered Cauchy probability measure. -/
theorem map_ordinate_uniformAngle {a : ℝ} (ha : 0 < a) :
    uniformAngle.map (ordinate a) = ProbabilityTheory.cauchyMeasure 0 (⟨a, ha.le⟩ : ℝ≥0) := by
  ext s hs
  have ha' : (⟨a, ha.le⟩ : ℝ≥0) ≠ 0 := fun h ↦ ha.ne' (congrArg (fun r : ℝ≥0 ↦ (r : ℝ)) h)
  have hd (t : ℝ) : ProbabilityTheory.cauchyPDF 0 (⟨a, ha.le⟩ : ℝ≥0) t =
      ENNReal.ofReal (density a t) := congrArg ENNReal.ofReal (cauchyPDFReal_zero (⟨a, ha.le⟩ : ℝ≥0) t)
  have hs' := (measurable_ordinate a) hs
  have h := lintegral_angle ha ((ordinate a ⁻¹' s).indicator (1 : ℝ → ℝ≥0∞))
  rw [lintegral_indicator_one hs'] at h
  rw [Measure.map_apply (measurable_ordinate a) hs, uniformAngle, smul_apply,
    smul_eq_mul, h, ProbabilityTheory.cauchyMeasure_of_scale_ne_zero 0 ha',
    withDensity_apply _ hs, ← lintegral_indicator hs]
  apply lintegral_congr
  intro t
  by_cases ht : t ∈ s <;>
    simp [Set.indicator, ht, ordinate_inverseAngle ha, hd]

instance isProbabilityMeasure_uniformAngle : IsProbabilityMeasure uniformAngle where
  measure_univ := by
    have h := congrArg (fun μ : Measure ℝ ↦ μ univ) (map_ordinate_uniformAngle zero_lt_one)
    have he : (ProbabilityTheory.cauchyMeasure 0 (⟨1, zero_le_one⟩ : ℝ≥0)) univ = 1 :=
      (ProbabilityTheory.instIsProbabilityMeasure_cauchyMeasure 0 _).measure_univ
    simpa only [Measure.map_apply (measurable_ordinate 1) MeasurableSet.univ, preimage_univ] using h.trans he

/-- The full complex pushforward lies on the line `Re z = b` with Cauchy-distributed ordinate. -/
theorem map_chart_uniformAngle (b : ℝ) {a : ℝ} (ha : 0 < a) :
    uniformAngle.map (fun θ ↦ chart b a (circleMap 0 1 θ)) =
      (ProbabilityTheory.cauchyMeasure 0 ⟨a, ha.le⟩).map (fun t : ℝ ↦ (b : ℂ) + t * I) := by
  rw [← map_ordinate_uniformAngle ha,
    Measure.map_map (by fun_prop : Measurable (fun t : ℝ ↦ (b : ℂ) + t * I)) (measurable_ordinate a)]
  congr 1
  funext θ
  exact chart_circleMap b a θ

/-- The normalized angular pushforward by the unsplit rational function, including
its exact center and scale. The value at `z = 1` is irrelevant to this measure identity. -/
theorem map_two_add_div_one_sub_uniformAngle :
    uniformAngle.map (fun θ ↦ (2 + circleMap 0 1 θ) / (1 - circleMap 0 1 θ)) =
      (ProbabilityTheory.cauchyMeasure 0 (3/2)).map (fun t : ℝ ↦ (1/2 : ℂ) + t * I) := by
  have h := map_chart_uniformAngle (1/2) (by norm_num : (0 : ℝ) < 3/2)
  have hs : (fun θ ↦ (2 + circleMap 0 1 θ) / (1 - circleMap 0 1 θ)) =ᵐ[uniformAngle]
      (fun θ ↦ chart (1/2) (3/2) (circleMap 0 1 θ)) := by
    unfold uniformAngle
    apply Measure.ae_smul_measure
    filter_upwards [ae_restrict_mem (μ := volume) (measurableSet_Ioo (a := (0 : ℝ)) (b := 2 * π))]
      with θ hθ
    exact two_add_div_one_sub_eq_chart (circleMap_ne_one hθ)
  have ha : (⟨(3/2 : ℝ), by norm_num⟩ : ℝ≥0) = 3/2 := by
    apply Subtype.ext
    change (3 : ℝ) / 2 = ((3/2 : ℝ≥0) : ℝ)
    simp only [NNReal.coe_div, NNReal.coe_ofNat]
  refine (Measure.map_congr hs).trans ?_
  simpa only [Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat, ha] using! h

/-- Extended integral for the map `(2 + z) / (1 - z)`, allowing infinite mass of the test. -/
theorem lintegral_two_add_div_one_sub (F : ℂ → ℝ≥0∞) :
    ENNReal.ofReal (2 * π)⁻¹ *
        ∫⁻ θ in Ioo 0 (2 * π), F ((2 + circleMap 0 1 θ) / (1 - circleMap 0 1 θ)) =
      ∫⁻ t : ℝ, ENNReal.ofReal ((3/2) / (π * ((3/2)^2 + t^2))) * F ((1/2 : ℂ) + t * I) := by
  simpa only [two_add_div_one_sub_inverseAngle, density] using
    lintegral_angle (by norm_num : (0 : ℝ) < 3/2)
      (fun θ ↦ F ((2 + circleMap 0 1 θ) / (1 - circleMap 0 1 θ)))

end RiemannMasullo.CayleyCauchy
