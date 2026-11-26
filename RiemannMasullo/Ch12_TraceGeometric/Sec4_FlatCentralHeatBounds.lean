module

public import RiemannMasullo.Ch12_TraceGeometric.Sec4_FlatMeanZeroHeat
public import RiemannMasullo.ForMathlib.Analysis.SpecialFunctions.Trigonometric.SincIntegral
import Mathlib.Analysis.Calculus.MeanValue

/-! Scalar and rank-one bounds for Gaussian displacements across the rational norm-one seam. -/

@[expose] public noncomputable section

open Filter MeasureTheory ProbabilityTheory Set Real
open scoped ENNReal NNReal InnerProductSpace CompactlySupported

namespace RiemannMasullo.ThroughOneStability

/-- Changing the scale of a sine integral costs at most the logarithmic displacement,
uniformly in the original phase, including at phase zero. -/
theorem sincPrimitive_logShift (a z : ℝ) :
    |(∫ v in (0 : ℝ)..a * exp z, sinc v) - ∫ v in (0 : ℝ)..a, sinc v| ≤ |z| := by
  let F (t : ℝ) := ∫ v in (0 : ℝ)..a * exp t, sinc v
  have hd (t : ℝ) : HasDerivAt F (sin (a * exp t)) t := by
    have hp := (continuous_sinc.integral_hasStrictDerivAt 0 (a * exp t)).hasDerivAt
    have h := hp.comp t ((hasDerivAt_exp t).const_mul a)
    apply h.congr_deriv
    rcases eq_or_ne a 0 with rfl | ha
    · simp
    · rw [sinc_of_ne_zero (mul_ne_zero ha (exp_pos t).ne'), div_mul_cancel₀ _ (mul_ne_zero ha (exp_pos t).ne')]
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := 0) (b := z)
    (fun t _ ↦ hd t) ((continuous_sin.comp (continuous_const.mul continuous_exp)).intervalIntegrable 0 z)
  have hb := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := z)
    (f := fun t : ℝ ↦ sin (a * exp t)) (C := 1)
    (fun t _ ↦ by simpa [Real.norm_eq_abs] using abs_le.mpr ⟨neg_one_le_sin _, sin_le_one _⟩)
  rw [hi] at hb
  simpa [F, Real.norm_eq_abs] using hb

/-- The direct scalar kernel at nonzero reciprocal phase. Its totalized value at zero
does not affect any of the spatial Haar averages. -/
def phaseKernel (R c : ℝ) : ℝ := (π * c)⁻¹ * ∫ t in (0 : ℝ)..(2 * π * c * R), sinc t

/-- After one phase zero, varying the band cutoff is uniformly logarithmically Lipschitz. -/
theorem phaseKernel_logShift_zeroWeight {C R c z y : ℝ} (hC : 0 ≤ C) (hy : |y| ≤ C * |c|) :
    |y * (phaseKernel (R * exp z) c - phaseKernel R c)| ≤ C / π * |z| := by
  by_cases hc : c = 0
  · simp [hc, phaseKernel]
    positivity
  have hsi := sincPrimitive_logShift (2 * π * c * R) z
  simp only [phaseKernel, ← mul_sub, abs_mul, abs_inv, abs_of_pos pi_pos]
  rw [← mul_assoc (2 * π * c) R (exp z)]
  calc
    |y| * ((π * |c|)⁻¹ * _) ≤ (C * |c|) * ((π * |c|)⁻¹ * |z|) := by
      gcongr
    _ = _ := by field_simp [hc, pi_ne_zero]

/-- The fixed-window universal reference is written in logarithmic band coordinates after
the exact Fubini identity of the sharp finite part. Additive constants drop out. -/
def logReference (δ u : ℝ) : ℝ :=
  (2 / π) * ∫ t in (0 : ℝ)..u, (∫ x in (0 : ℝ)..(2 * π * δ * exp t), sinc x)

/-- The reference changes by a controlled quantity even though its value grows like log R. -/
theorem logReference_move (δ u v : ℝ) :
    |logReference δ v - logReference δ u| ≤ (2/π) * (π / 2 + 2) * |v-u| := by
  let F (t : ℝ) := ∫ x in (0 : ℝ)..(2 * π * δ * exp t), sinc x
  have hf : Continuous F := continuous_integral_sinc.comp (continuous_const.mul continuous_exp)
  have h := intervalIntegral.integral_add_adjacent_intervals (μ := volume) (hf.intervalIntegrable 0 u) (hf.intervalIntegrable u v)
  have hb := intervalIntegral.norm_integral_le_of_norm_le_const (a := u) (b := v) (f := F)
    (C := π/2+2) (fun t _ ↦ by simpa only [F, Real.norm_eq_abs] using abs_integral_sinc_le (2*π*δ*exp t))
  change |(2/π)*(∫ t in (0:ℝ)..v, F t) - (2/π)*(∫ t in (0:ℝ)..u, F t)| ≤ _
  rw [← h, ← mul_sub, add_sub_cancel_left, abs_mul, abs_of_pos (by positivity : 0 < 2/π), mul_assoc]
  exact mul_le_mul_of_nonneg_left hb (by positivity)

/-- A bounded second log derivative controls the translated profile after removal of its
value at the shifted seam. Both factors are retained, so integration against 1/|c| is harmless. -/
theorem logProfile_mixed_displacement (W V : ℝ → ℝ) (K : ℝ)
    (hW : ∀ t, HasDerivAt W (V t) t) (hV : ∀ t u, |V t-V u| ≤ K * |t-u|)
    (x z : ℝ) : |W (x-z)-W x-(W (-z)-W 0)| ≤ K * |z| * |x| := by
  let G (t : ℝ) := W (t-z) - W t
  have hG (t : ℝ) : HasDerivAt G (V (t-z)-V t) t := by
    have h := ((hW (t-z)).comp t ((hasDerivAt_id' t).sub_const z)).fun_sub (hW t)
    simpa only [G, Function.comp_def, mul_one] using h
  have h := (convex_univ (𝕜 := ℝ) (E := ℝ)).norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun t _ ↦ (hG t).hasDerivWithinAt) (fun t _ ↦ by
      have h' := hV (t-z) t
      rw [show t-z-t = -z by ring, abs_neg] at h'
      simpa only [Real.norm_eq_abs] using h') (mem_univ (0 : ℝ)) (mem_univ x)
  simpa only [G, Real.norm_eq_abs, zero_sub, sub_zero] using h

end RiemannMasullo.ThroughOneStability

namespace RiemannMasullo.FlatPolar

local notation "H" => Lp ℂ 2 (volume.restrict (Ioi (0 : ℝ)))

private theorem heatCorrection_bound {B : ℝ} (hB : 0 < B) (h L : ℝ) (τ : ℝ≥0) (φ : C_c(ℝ≥0ˣ, ℂ)) :
    let T := (spatialCutoffInChart positiveRayInverseCosine h L).comp (compactDilationAction φ)
    ‖hilbertTrace (logHeatSandwich τ (meanZeroCompactCosineTraceOperator h L B φ)) -
      hilbertTrace (logHeatSandwich τ (compactCosineTraceOperator 0 B h L φ)) +
      ⟪bandVector B, T (bandVector B)⟫_ℂ‖ ≤ 2 * ‖T‖ * Real.sqrt (Real.sqrt ((τ+τ : ℝ≥0) : ℝ)) := by
  let T := (spatialCutoffInChart positiveRayInverseCosine h L).comp (compactDilationAction φ)
  let A := compactCosineTraceOperator 0 B h L φ
  let M := meanZeroCompactCosineTraceOperator h L B φ
  obtain ⟨Q, hQ, htr⟩ := exists_sandwich_compressionDifference (logHeat τ) T (isSelfAdjoint_logHeat τ)
    (frequencyBand B) (norm_bandVector hB) (bandVector_mem_frequencyBand B)
  have he : Q = logHeatSandwich τ M - logHeatSandwich τ A := by
    apply Subtype.ext
    exact (hQ.trans (sandwich_compressionDifference_eq_two_rows (logHeat τ) T (isSelfAdjoint_logHeat τ)
      (frequencyBand B) (norm_bandVector hB))).trans (meanZeroCompactCosine_heatDifference_eq_two_rows hB h L τ φ).symm
  obtain ⟨tr, htr'⟩ := hilbertTrace_linear («H» := H)
  have hQtr : hilbertTrace Q = hilbertTrace (logHeatSandwich τ M) - hilbertTrace (logHeatSandwich τ A) := by
    exact (congrArg hilbertTrace he).trans ((htr' _).symm.trans
      ((map_sub tr (logHeatSandwich τ M) (logHeatSandwich τ A)).trans
        (congrArg₂ (fun x y : ℂ ↦ x-y) (htr' _) (htr' _))))
  rw [hQtr, ← logHeat_add τ τ (bandVector B)] at htr
  exact htr.trans (mul_le_mul_of_nonneg_left
    ((Real.le_sqrt (norm_nonneg _) (Real.sqrt_nonneg _)).mpr (norm_logHeat_sub_bandVector_sq_le (τ+τ) hB)) (by positivity))

/-- The motion of the actual removed mean row is uniform even when the radial window crosses
one. The cold and hot compressions have the same spatial floor and ceiling. -/
theorem centralWindow_meanZeroHeat_cold_difference {B : ℝ} (hB : 0 < B) (h L : ℝ) (τ : ℝ≥0)
    (φ : C_c(ℝ≥0ˣ, ℂ)) :
    let M := meanZeroCompactCosineTraceOperator h L B φ
    let A := compactCosineTraceOperator 0 B h L φ
    ‖(hilbertTrace (logHeatSandwich τ M) - hilbertTrace (logHeatSandwich τ A)) -
      (hilbertTrace (logHeatSandwich 0 M) - hilbertTrace (logHeatSandwich 0 A))‖ ≤
      2 * ‖compactDilationAction φ‖ * Real.sqrt (Real.sqrt ((τ + τ : ℝ≥0) : ℝ)) := by
  let V := positiveRayInverseCosine
  let U := compactDilationAction φ
  let T := (spatialCutoffInChart positiveRayInverseCosine h L).comp U
  let k := ⟪bandVector B, T (bandVector B)⟫_ℂ
  let C (t : ℝ≥0) := hilbertTrace (logHeatSandwich t (meanZeroCompactCosineTraceOperator h L B φ)) -
    hilbertTrace (logHeatSandwich t (compactCosineTraceOperator 0 B h L φ))
  have hc : C 0 + k = 0 := by
    have h0 := heatCorrection_bound hB h L 0 φ
    change ‖C 0 + k‖ ≤ _ at h0
    exact norm_le_zero_iff.mp (by simpa using h0)
  have hV : ‖spatialCutoffInChart V h L‖ ≤ 1 := calc
    _ ≤ ‖V.toContinuousLinearMap.adjoint‖ * ‖(spatialCutoff h L).comp V.toContinuousLinearMap‖ :=
      ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ 1 * (1 * 1) := by
      apply mul_le_mul _ _ (norm_nonneg _) zero_le_one
      · simpa only [ContinuousLinearMap.adjoint.norm_map] using V.norm_toContinuousLinearMap_le
      · exact (ContinuousLinearMap.opNorm_comp_le _ _).trans (mul_le_mul (norm_spatialCutoff_le _ _)
          V.norm_toContinuousLinearMap_le (norm_nonneg _) zero_le_one)
    _ = _ := by norm_num
  have hT : ‖T‖ ≤ ‖U‖ := (ContinuousLinearMap.opNorm_comp_le _ _).trans
    ((mul_le_mul_of_nonneg_right hV (norm_nonneg U)).trans_eq (one_mul _))
  change ‖C τ - C 0‖ ≤ _
  rw [show C 0 = -k by exact eq_neg_of_add_eq_zero_left hc, sub_neg_eq_add]
  exact (heatCorrection_bound hB h L τ φ).trans
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hT (by norm_num)) (by positivity))

end RiemannMasullo.FlatPolar
