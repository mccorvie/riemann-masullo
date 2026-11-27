module

public import RiemannMasullo.Ch12_TraceGeometric.Sec4_FlatCompactCosineShift
public import RiemannMasullo.Ch12_TraceGeometric.Sec4_FlatCosineTraceLimit
import RiemannMasullo.ForMathlib.MeasureTheory.Group.Arithmetic

/-!
# Removing both real-even cutoffs under a compact radial test

The quantitative finite-atom bound is integrated in Haar measure. It is uniform
in every shift for which the translated support stays in the same positive compact
set away from one. On a compact interval strictly above one, the orbital value
is continuous under small shifts.
-/

@[expose] public noncomputable section

open Filter MeasureTheory Set
open scoped CompactlySupported NNReal Topology

namespace RiemannMasullo.FlatPolar

/-- The full real-even orbital value, averaged against the original compact test
after translating the dilation parameter by `r`. -/
def compactCosineOrbitalValue (φ : C_c(ℝ≥0ˣ, ℂ)) (r : ℝ≥0ˣ) : ℂ :=
  ∫ a : ℝ≥0ˣ, φ a * (finiteCosineDilationValue (a * r).val : ℂ) ∂positiveRealHaar

private theorem continuousOn_finiteCosineDilationValue {J : Set ℝ}
    (hpar : ∀ a ∈ J, 0 < a ∧ a ≠ 1) : ContinuousOn finiteCosineDilationValue J := by
  intro a ha
  obtain ⟨ha₀, ha₁⟩ := hpar a ha
  have hm : 1 - a⁻¹ ≠ 0 := by
    intro h
    have : a⁻¹ = 1 := by linarith
    exact ha₁ (inv_eq_one.mp this)
  have hp : 1 + a⁻¹ ≠ 0 := by positivity
  have hs : Real.sqrt a ≠ 0 := (Real.sqrt_pos.mpr ha₀).ne'
  apply ContinuousAt.continuousWithinAt
  unfold finiteCosineDilationValue
  fun_prop (disch := first | positivity | assumption | exact abs_ne_zero.mpr hm)

private theorem integrable_compactRadialProduct (φ : C_c(ℝ≥0ˣ, ℂ)) {F : ℝ≥0ˣ → ℂ}
    (hF : ContinuousOn F (tsupport φ)) :
    Integrable (fun a ↦ φ a * F a) positiveRealHaar := by
  let : BorelSpace ℝ≥0ˣ := borelSpace_units_of_continuousInv₀ ℝ≥0
  let : positiveRealHaar.IsHaarMeasure := positiveRealHaar_isHaarMeasure
  apply (integrableOn_iff_integrable_of_support_subset
    ((Function.support_mul_subset_left φ F).trans (subset_tsupport _))).mp
  exact (φ.continuous.continuousOn.mul hF).integrableOn_compact' φ.hasCompactSupport
    (isClosed_tsupport _).measurableSet

/-- A bound uniform in the compact test's multiplicative shift whenever its shifted
support fits in `J`. The constant is the atomic constant times the Haar L¹ norm of the test. -/
theorem exists_hilbertTrace_compactCosineShift_error_const
    {J : Set ℝ} (hJ : IsCompact J) (hpar : ∀ a ∈ J, 0 < a ∧ a ≠ 1) (φ : C_c(ℝ≥0ˣ, ℂ)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ r : ℝ≥0ˣ, (∀ a ∈ tsupport φ, ((a * r).val : ℝ) ∈ J) →
      ∀ {h L B : ℝ}, 0 ≤ h → 0 < L → h ≤ L → 0 < B →
      ‖hilbertTrace (compactCosineTraceOperator 0 B h L (compactRadialTranslate φ r)) -
        compactCosineOrbitalValue φ r‖ ≤ C * (B * h + (B * L)⁻¹) := by
  let : BorelSpace ℝ≥0ˣ := borelSpace_units_of_continuousInv₀ ℝ≥0
  let : positiveRealHaar.IsHaarMeasure := positiveRealHaar_isHaarMeasure
  obtain ⟨C, hC₀, hC⟩ := exists_hilbertTrace_frequencyBand_error_const hJ hpar
  let N := ∫ a : ℝ≥0ˣ, ‖φ a‖ ∂positiveRealHaar
  have hN : 0 ≤ N := integral_nonneg (fun _ ↦ norm_nonneg _)
  refine ⟨N * C, mul_nonneg hN hC₀, ?_⟩
  intro r hr h L B hh hL hhL hB
  let T (a : ℝ≥0ˣ) := hilbertTrace (finiteCosineTraceOperator 0 B h L (a * r).val)
  let V (a : ℝ≥0ˣ) : ℂ := finiteCosineDilationValue (a * r).val
  have hT : Continuous T :=
    (continuous_hilbertTrace_finiteCosineTraceOperator 0 B h L).comp (continuous_id.mul continuous_const)
  have hc : Continuous (fun a : ℝ≥0ˣ ↦ ((a * r).val : ℝ)) :=
    (NNReal.continuous_coe.comp Units.continuous_val).comp (continuous_id.mul continuous_const)
  have hV : ContinuousOn V (tsupport φ) :=
    Complex.continuous_ofReal.comp_continuousOn ((continuousOn_finiteCosineDilationValue hpar).comp hc.continuousOn hr)
  rw [hilbertTrace_compactCosineTraceOperator_shift]
  change ‖(∫ a, φ a * T a ∂positiveRealHaar) - ∫ a, φ a * V a ∂positiveRealHaar‖ ≤ _
  rw [← integral_sub (integrable_compactRadialProduct φ hT.continuousOn) (integrable_compactRadialProduct φ hV)]
  let e := C * (B * h + (B * L)⁻¹)
  have hφ := φ.continuous.integrable_of_hasCompactSupport (μ := positiveRealHaar) φ.hasCompactSupport
  calc
    _ ≤ ∫ a, ‖φ a * T a - φ a * V a‖ ∂positiveRealHaar := norm_integral_le_integral_norm _
    _ ≤ ∫ a, ‖φ a‖ * e ∂positiveRealHaar := by
      apply integral_mono_of_nonneg (.of_forall (fun _ ↦ norm_nonneg _)) (hφ.norm.mul_const e)
      filter_upwards with a
      by_cases ha : a ∈ tsupport φ
      · rw [← mul_sub, norm_mul]
        exact mul_le_mul_of_nonneg_left (hC _ (hr a ha) hh hL hhL hB) (norm_nonneg _)
      · simp [image_eq_zero_of_notMem_tsupport ha]
    _ = _ := by rw [integral_mul_const]; dsimp only [N, e]; ring

/-- The finite-cutoff error vanishes jointly for varying shifts as long as all shifted
supports eventually stay in one compact positive set away from one. -/
theorem tendsto_hilbertTrace_compactCosineShift_sub_orbital {ι : Type*} {l : Filter ι}
    {h L B : ι → ℝ} {r : ι → ℝ≥0ˣ} {J : Set ℝ} (hJ : IsCompact J)
    (hpar : ∀ a ∈ J, 0 < a ∧ a ≠ 1) (φ : C_c(ℝ≥0ˣ, ℂ))
    (hr : ∀ᶠ i in l, ∀ a ∈ tsupport φ, ((a * r i).val : ℝ) ∈ J)
    (hbox : ∀ᶠ i in l, 0 ≤ h i ∧ 0 < B i)
    (hBh : Tendsto (fun i ↦ B i * h i) l (𝓝 0)) (hBL : Tendsto (fun i ↦ B i * L i) l atTop) :
    Tendsto (fun i ↦ hilbertTrace (compactCosineTraceOperator 0 (B i) (h i) (L i)
      (compactRadialTranslate φ (r i))) - compactCosineOrbitalValue φ (r i)) l (𝓝 0) := by
  obtain ⟨C, _, hC⟩ := exists_hilbertTrace_compactCosineShift_error_const hJ hpar φ
  apply squeeze_zero_norm' (a := fun i ↦ C * (B i * h i + (B i * L i)⁻¹))
  · filter_upwards [hbox, hr, hBh.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1)),
      hBL.eventually_gt_atTop 1] with i hi hri hb₁ hb₂
    have hL : 0 < L i := pos_of_mul_pos_right (by linarith : 0 < B i * L i) hi.2.le
    have hhL : h i ≤ L i := (lt_of_mul_lt_mul_left (hb₁.trans hb₂) hi.2.le).le
    exact hC _ hri hi.1 hL hhL hi.2
  · simpa using (hBh.add (tendsto_inv_atTop_zero.comp hBL)).const_mul C

private theorem shifted_support_lower {η : ℝ} (hη : 0 < η) :
    ∀ᶠ r : ℝ≥0ˣ in 𝓝 1, 1 + η / 2 < (1 + η) * (r.val : ℝ) := by
  have hc : Continuous (fun r : ℝ≥0ˣ ↦ (1 + η) * (r.val : ℝ)) :=
    continuous_const.mul (NNReal.continuous_coe.comp Units.continuous_val)
  exact (hc.tendsto 1).eventually_const_lt (by simp; linarith)

/-- A support with a positive gap above the identity gives continuity of the limiting
orbital integral at shift one. Both the test and its limiting integral may be complex. -/
theorem continuousAt_compactCosineOrbitalValue_one (φ : C_c(ℝ≥0ˣ, ℂ)) {η : ℝ} (hη : 0 < η)
    (hs : ∀ a ∈ tsupport φ, 1 + η ≤ (a.val : ℝ)) :
    ContinuousAt (compactCosineOrbitalValue φ) 1 := by
  let c := 1 + η / 2
  have hc : 1 < c := by dsimp [c]; linarith
  let u (b : ℝ≥0ˣ) := max c (b.val : ℝ)
  let F (b : ℝ≥0ˣ) : ℂ := (u b * Real.sqrt (u b) / ((u b)^2 - 1) : ℝ)
  have hu : Continuous u := continuous_const.max (NNReal.continuous_coe.comp Units.continuous_val)
  have hden (b : ℝ≥0ˣ) : (u b)^2 - 1 ≠ 0 := by
    have hb : 1 < u b := hc.trans_le (le_max_left _ _)
    have hp : 0 < u b + 1 := by linarith
    nlinarith [mul_pos (sub_pos.mpr hb) hp]
  have hF : Continuous F :=
    Complex.continuous_ofReal.comp ((hu.mul (Real.continuous_sqrt.comp hu)).div (hu.pow 2 |>.sub continuous_const) hden)
  have heq : compactCosineOrbitalValue φ =ᶠ[𝓝 1]
      (fun r : ℝ≥0ˣ ↦ ∫ a : ℝ≥0ˣ, φ a * F (a * r) ∂positiveRealHaar) := by
    filter_upwards [shifted_support_lower hη] with r hr
    apply integral_congr_ae
    filter_upwards with a
    by_cases ha : a ∈ tsupport φ
    · have he : c ≤ ((a * r).val : ℝ) :=
        hr.le.trans (mul_le_mul_of_nonneg_right (hs a ha) r.val.2)
      apply congrArg (φ a * ·)
      change (finiteCosineDilationValue ((a * r).val : ℝ) : ℂ) =
        ((max c ((a * r).val : ℝ) * Real.sqrt (max c ((a * r).val : ℝ)) /
          ((max c ((a * r).val : ℝ)) ^ 2 - 1) : ℝ) : ℂ)
      rw [max_eq_right he, finiteCosineDilationValue_of_one_lt (hc.trans_le he)]
    · simp [image_eq_zero_of_notMem_tsupport ha]
  exact (continuous_compactRadialShiftIntegral φ hF).continuousAt.congr_of_eventuallyEq heq

/-- The genuine finite trace for compact tests supported in `[1+η,M]` converges to
the full unshifted orbital value jointly with removal of the windows and small
multiplicative translations. -/
theorem tendsto_hilbertTrace_compactCosineShift_frequencyBand {ι : Type*} {l : Filter ι}
    {h L B : ι → ℝ} {r : ι → ℝ≥0ˣ} (φ : C_c(ℝ≥0ˣ, ℂ)) {η M : ℝ} (hη : 0 < η)
    (hs : ∀ a ∈ tsupport φ, (a.val : ℝ) ∈ Icc (1 + η) M)
    (hr : Tendsto r l (𝓝 1)) (hbox : ∀ᶠ i in l, 0 ≤ h i ∧ 0 < B i)
    (hBh : Tendsto (fun i ↦ B i * h i) l (𝓝 0)) (hBL : Tendsto (fun i ↦ B i * L i) l atTop) :
    Tendsto (fun i ↦ hilbertTrace (compactCosineTraceOperator 0 (B i) (h i) (L i)
      (compactRadialTranslate φ (r i)))) l (𝓝 (compactCosineOrbitalValue φ 1)) := by
  let J := Icc (1 + η / 2) (2 * max M 1)
  have hpar (a : ℝ) (ha : a ∈ J) : 0 < a ∧ a ≠ 1 := by
    have hlow := ha.1
    constructor <;> linarith
  have hru : ∀ᶠ i in l, ((r i).val : ℝ) < 2 :=
    (((NNReal.continuous_coe.comp Units.continuous_val).tendsto (1 : ℝ≥0ˣ)).comp hr).eventually_lt_const (by norm_num)
  have hJ : ∀ᶠ i in l, ∀ a ∈ tsupport φ, ((a * r i).val : ℝ) ∈ J := by
    filter_upwards [hr.eventually (shifted_support_lower hη), hru] with i hi hi'
    intro a ha
    change (1 + η / 2 ≤ (a.val : ℝ) * ((r i).val : ℝ)) ∧ (a.val : ℝ) * ((r i).val : ℝ) ≤ 2 * max M 1
    refine ⟨hi.le.trans (mul_le_mul_of_nonneg_right (hs a ha).1 (r i).val.2), ?_⟩
    rw [mul_comm (2 : ℝ)]
    exact mul_le_mul ((hs a ha).2.trans (le_max_left _ _)) hi'.le (r i).val.2 (le_trans zero_le_one (le_max_right _ _))
  have he := tendsto_hilbertTrace_compactCosineShift_sub_orbital (J := J) isCompact_Icc hpar φ hJ hbox hBh hBL
  have hv := (continuousAt_compactCosineOrbitalValue_one φ hη (fun a ha ↦ (hs a ha).1)).tendsto.comp hr
  simpa using he.add hv

/-- The original unshifted compact-test trace on the full finite band has the sharp
orbital limit for every positive gap above one. -/
theorem tendsto_hilbertTrace_compactCosine_frequencyBand {ι : Type*} {l : Filter ι}
    {h L B : ι → ℝ} (φ : C_c(ℝ≥0ˣ, ℂ)) {η M : ℝ} (hη : 0 < η)
    (hs : ∀ a ∈ tsupport φ, (a.val : ℝ) ∈ Icc (1 + η) M)
    (hbox : ∀ᶠ i in l, 0 ≤ h i ∧ 0 < B i)
    (hBh : Tendsto (fun i ↦ B i * h i) l (𝓝 0)) (hBL : Tendsto (fun i ↦ B i * L i) l atTop) :
    Tendsto (fun i ↦ hilbertTrace (compactCosineTraceOperator 0 (B i) (h i) (L i) φ))
      l (𝓝 (∫ a : ℝ≥0ˣ, φ a * (finiteCosineDilationValue a.val : ℂ) ∂positiveRealHaar)) := by
  simpa [compactCosineOrbitalValue] using tendsto_hilbertTrace_compactCosineShift_frequencyBand
    (r := fun _ ↦ 1) φ hη hs tendsto_const_nhds hbox hBh hBL

end RiemannMasullo.FlatPolar
