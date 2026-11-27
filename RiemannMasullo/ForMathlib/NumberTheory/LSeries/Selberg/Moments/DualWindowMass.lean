module

public import RiemannMasullo.ForMathlib.NumberTheory.LSeries.Selberg.Definitions
import RiemannMasullo.ForMathlib.NumberTheory.LSeries.Selberg.Arithmetic.TaperSpec
import RiemannMasullo.ForMathlib.NumberTheory.LSeries.Selberg.Fourier.DualEnvelope
import RiemannMasullo.ForMathlib.NumberTheory.LSeries.Selberg.Moments.DualWeighted
import RiemannMasullo.ForMathlib.NumberTheory.LSeries.Selberg.Moments.MultLaplace

public section

open MeasureTheory Set

namespace RiemannMasullo.Selberg

private lemma integrable_sq_of_envelope {f : ℝ → ℂ} (hc : Continuous f) {A : ℝ}
    (hbound : ∀ y, ‖f y‖ ≤ A * Real.exp (-|y| / 2)) :
    Integrable (fun y : ℝ ↦ ‖f y‖ ^ 2) := by
  have hdecay : Integrable (fun y : ℝ ↦ Real.exp (-|y|)) := by
    rw [← integrableOn_univ, ← Iic_union_Ioi (a := (0 : ℝ)), integrableOn_union]
    constructor
    · apply (integrableOn_exp_Iic 0).congr_fun _ measurableSet_Iic
      intro y hy
      simp [abs_of_nonpos hy]
    · apply (integrableOn_exp_neg_Ioi 0).congr_fun _ measurableSet_Ioi
      intro y hy
      simp [abs_of_nonneg hy.le]
  apply (hdecay.const_mul (A^2)).mono' (hc.norm.pow 2).aestronglyMeasurable
  refine ae_of_all _ fun y ↦ ?_
  change ‖‖f y‖ ^ 2‖ ≤ A^2 * Real.exp (-|y|)
  rw [Real.norm_of_nonneg (sq_nonneg _)]
  calc
    _ ≤ (A * Real.exp (-|y| / 2))^2 :=
      pow_le_pow_left₀ (norm_nonneg _) (hbound y) 2
    _ = _ := by rw [mul_pow, sq (Real.exp _), ← Real.exp_add, add_halves]

/-- Card 41. For 0 < h ≤ 1/2 the squared norm integral of the tapered dual times the window
multiplier is bounded by a constant times h N⁵⁰/log N.
Replacement integral for the end of Titchmarsh Lemma 10.17, pp. 275–276. -/
theorem dual_window_mass : ∃ C > (0 : ℝ), ∀ N : ℕ, 2 ≤ N → ∀ h : ℝ, 0 < h → h ≤ 1/2 →
    (∫ y : ℝ, ‖dual N (beta N) y * mult h y‖^2) ≤ C*h*(N : ℝ)^50/Real.log N := by
  obtain ⟨B, hB, hmass⟩ := dual_weighted
  refine ⟨8 * Real.exp 1 * B, by positivity, ?_⟩
  intro N hN h hh hh'
  obtain ⟨_, _, henv⟩ := dual_envelope
  obtain ⟨hc, hbound⟩ := henv N hN _ (taper_spec N hN).2
  let F (q y : ℝ) := q * Real.exp (-q * |y|) * ‖dual N (beta N) y‖^2
  let μ := volume.restrict (Ioc 0 h)
  -- On (0,h] the damping factor is at most one, so q times the squared dual dominates F.
  have hF : Integrable (Function.uncurry F) (μ.prod volume) := by
    have hq : Integrable (fun q : ℝ ↦ q) μ :=
      continuous_id.integrableOn_Icc.mono_set Ioc_subset_Icc_self
    apply (hq.mul_prod (integrable_sq_of_envelope hc hbound)).mono'
    · apply Continuous.aestronglyMeasurable
      dsimp [Function.uncurry, F]
      fun_prop
    · have hmem : ∀ᵐ p : ℝ × ℝ ∂μ.prod volume, p.1 ∈ Ioc 0 h :=
        Measure.quasiMeasurePreserving_fst.ae (ae_restrict_mem measurableSet_Ioc)
      filter_upwards [hmem] with p hp
      have hq0 := hp.1.le
      dsimp [Function.uncurry, F]
      rw [abs_of_nonneg (by positivity)]
      apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
      exact mul_le_of_le_one_right hq0 (Real.exp_le_one_iff.mpr
        (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hq0) (abs_nonneg _)))
  have hmajor (y : ℝ) : ‖dual N (beta N) y * mult h y‖^2 ≤
      8 * Real.exp 1 * ∫ q, F q y ∂μ := by
    have hm := mult_laplace h y hh
    rw [intervalIntegral.integral_of_le hh.le] at hm
    dsimp [F, μ]
    rw [integral_mul_const, norm_mul, mul_pow]
    calc
      _ ≤ ‖dual N (beta N) y‖^2 * _ := mul_le_mul_of_nonneg_left hm (sq_nonneg _)
      _ = _ := by ring
  have hinner (q : ℝ) : (∫ y, F q y) = q * dualMass N q := by
    simp only [F, dualMass, mul_assoc, integral_const_mul]
  have hmult : Continuous (mult h) := by
    unfold mult osc
    fun_prop
  have hint := hF.integral_prod_right.const_mul (8 * Real.exp 1)
  calc
    _ ≤ ∫ y, 8 * Real.exp 1 * ∫ q, F q y ∂μ := by
      apply integral_mono _ hint hmajor
      apply hint.mono' ((hc.mul hmult).norm.pow 2).aestronglyMeasurable
      exact ae_of_all _ fun y ↦ (Real.norm_of_nonneg (sq_nonneg _)).trans_le (hmajor y)
    _ = 8 * Real.exp 1 * ∫ q, ∫ y, F q y ∂volume ∂μ := by
      rw [integral_const_mul, integral_integral_swap hF]
    _ ≤ 8 * Real.exp 1 * ∫ _, B*(N : ℝ)^50/Real.log N ∂μ := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply integral_mono_ae hF.integral_prod_left (integrable_const _)
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with q hq
      rw [Function.uncurry_def, hinner]
      -- Every q in (0,h] is positive, so it cancels the denominator in the mass bound.
      calc
        _ ≤ q * (B*(N : ℝ)^50/(q*Real.log N)) :=
          mul_le_mul_of_nonneg_left (hmass N hN q hq.1 (hq.2.trans hh')) hq.1.le
        _ = _ := by field_simp [ne_of_gt hq.1]
    _ = _ := by
      dsimp [μ]
      rw [setIntegral_const, Real.volume_real_Ioc_of_le hh.le, sub_zero, smul_eq_mul]
      ring

end RiemannMasullo.Selberg
