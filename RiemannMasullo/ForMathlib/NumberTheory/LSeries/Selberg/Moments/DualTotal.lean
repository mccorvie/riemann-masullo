module

public import RiemannMasullo.ForMathlib.NumberTheory.LSeries.Selberg.Definitions
import RiemannMasullo.ForMathlib.NumberTheory.LSeries.Selberg.Arithmetic.TaperSpec
import RiemannMasullo.ForMathlib.NumberTheory.LSeries.Selberg.Fourier.DualEnvelope
import RiemannMasullo.ForMathlib.NumberTheory.LSeries.Selberg.Moments.DualWeighted
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

public section

open MeasureTheory Set

namespace RiemannMasullo.Selberg

/-- On the central interval the weight can be removed at a cost of a factor of
`exp 1`. The two exponential tails each contribute at most `A * exp (-L)`. -/
private lemma remove_exp_weight {f : ℝ → ℝ} (hf : Continuous f) (hf₀ : ∀ y, 0 ≤ f y)
    {A L : ℝ} (hL : 0 < L) (henv : ∀ y, f y ≤ A * Real.exp (-|y|)) :
    (∫ y, f y) ≤ Real.exp 1 * (∫ y, Real.exp (-L⁻¹ * |y|) * f y) +
      A * (2 * Real.exp (-L)) := by
  let tail := (Ioi L).indicator (fun r : ℝ ↦ Real.exp (-r))
  have htail : (∫ y : ℝ, tail |y|) = 2 * Real.exp (-L) := by
    dsimp only [tail]
    rw [integral_comp_abs, integral_indicator measurableSet_Ioi,
      Measure.restrict_restrict measurableSet_Ioi, inter_eq_left.mpr (Ioi_subset_Ioi hL.le),
      integral_exp_neg_Ioi]
  have htailInt : Integrable (fun y : ℝ ↦ tail |y|) :=
    .of_integral_ne_zero (by rw [htail]; positivity)
  have hexpInt : Integrable (fun y : ℝ ↦ Real.exp (-|y|)) := by
    apply Integrable.of_integral_ne_zero
    rw [integral_comp_abs (f := fun r ↦ Real.exp (-r)), integral_exp_neg_Ioi_zero]
    norm_num
  have hfInt : Integrable f :=
    (hexpInt.const_mul A).mono' hf.aestronglyMeasurable
      (ae_of_all _ fun y ↦ by simpa only [Real.norm_of_nonneg (hf₀ y)] using henv y)
  let w := fun y : ℝ ↦ Real.exp (-L⁻¹ * |y|) * f y
  have hw₀ (y : ℝ) : 0 ≤ w y := mul_nonneg (Real.exp_pos _).le (hf₀ y)
  have hwInt : Integrable w := by
    refine hfInt.mono' (show Continuous w by dsimp [w]; fun_prop).aestronglyMeasurable ?_
    refine ae_of_all _ fun y ↦ ?_
    rw [Real.norm_of_nonneg (hw₀ y)]
    apply mul_le_of_le_one_left (hf₀ y)
    rw [Real.exp_le_one_iff, neg_mul, neg_nonpos]
    positivity
  calc
    (∫ y, f y) ≤ ∫ y, Real.exp 1 * w y + A * tail |y| := by
      apply integral_mono hfInt ((hwInt.const_mul _).add (htailInt.const_mul _))
      intro y
      change f y ≤ Real.exp 1 * w y + A * tail |y|
      by_cases hy : |y| ≤ L
      · simp only [tail, indicator_of_notMem (show |y| ∉ Ioi L from not_lt.mpr hy),
          mul_zero, add_zero, w, ← mul_assoc, ← Real.exp_add]
        apply le_mul_of_one_le_left (hf₀ y)
        apply Real.one_le_exp_iff.mpr
        have := mul_le_mul_of_nonneg_left hy (inv_nonneg.mpr hL.le)
        rw [inv_mul_cancel₀ hL.ne'] at this
        linarith
      · rw [show tail |y| = Real.exp (-|y|) from indicator_of_mem (lt_of_not_ge hy) _]
        exact (henv y).trans (le_add_of_nonneg_left (mul_nonneg (Real.exp_pos _).le (hw₀ y)))
    _ = _ := by
      rw [integral_add (hwInt.const_mul _) (htailInt.const_mul _), integral_const_mul,
        integral_const_mul, htail]

/-- Card 36. The unweighted squared norm integral of the tapered dual is bounded by a constant
times N⁵⁰ for N ≥ 2.
Titchmarsh, Lemma 10.18, pp. 276–277. -/
theorem dual_total : ∃ C > (0 : ℝ), ∀ N : ℕ, 2 ≤ N →
    (∫ y : ℝ, ‖dual N (beta N) y‖^2) ≤ C*(N : ℝ)^50 := by
  obtain ⟨B, hB, hweighted⟩ := dual_weighted
  obtain ⟨E, hE, henvelope⟩ := dual_envelope
  refine ⟨Real.exp 1 * (200 * B) + 2 * E^2, by positivity, ?_⟩
  intro N hN
  have hN₂ : 2 ≤ (N : ℝ) := by exact_mod_cast hN
  have hN₁ : 1 ≤ (N : ℝ) := by linarith
  have hlog : 0 < Real.log N := Real.log_pos (by linarith)
  let L := 200 * Real.log N
  have hL : 0 < L := by dsimp [L]; positivity
  have hq : L⁻¹ ≤ 1/2 := by
    have hlog₂ := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
    have hmono := Real.log_le_log (by norm_num : (0 : ℝ) < 2) hN₂
    rw [inv_eq_one_div, div_le_iff₀ hL]
    dsimp [L]
    norm_num at hlog₂
    linarith
  have hmass := hweighted N hN L⁻¹ (inv_pos.mpr hL) hq
  have hden : L⁻¹ * Real.log N = 1/200 := by
    dsimp [L]
    field_simp [hlog.ne']
  rw [hden] at hmass
  obtain ⟨hcont, hbound⟩ := henvelope N hN (beta N) (taper_spec N hN).2
  have hsq (y : ℝ) : ‖dual N (beta N) y‖^2 ≤
      (E * (N : ℝ)^53)^2 * Real.exp (-|y|) := calc
    _ ≤ (E * (N : ℝ)^53 * Real.exp (-|y|/2))^2 :=
      pow_le_pow_left₀ (norm_nonneg _) (hbound y) 2
    _ = _ := by rw [mul_pow, sq (Real.exp _), ← Real.exp_add]; ring_nf
  have hexp : Real.exp (-L) = ((N : ℝ)^200)⁻¹ := by
    rw [Real.exp_neg, show L = Real.log ((N : ℝ)^200) by rw [Real.log_pow]; rfl,
      Real.exp_log (by positivity)]
  have htail : (E * (N : ℝ)^53)^2 * (2 * Real.exp (-L)) ≤ 2 * E^2 * (N : ℝ)^50 := by
    rw [hexp]
    calc
      _ = (2 * E^2 * (N : ℝ)^106) / (N : ℝ)^200 := by ring
      _ ≤ 2 * E^2 := by
        apply (div_le_iff₀ (by positivity)).mpr
        exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hN₁ (by decide)) (by positivity)
      _ ≤ _ := le_mul_of_one_le_right (by positivity) (one_le_pow₀ hN₁)
  calc
    _ ≤ Real.exp 1 * dualMass N L⁻¹ + (E * (N : ℝ)^53)^2 * (2 * Real.exp (-L)) :=
      remove_exp_weight (hcont.norm.pow 2) (fun y ↦ sq_nonneg _) hL hsq
    _ ≤ Real.exp 1 * (B * (N : ℝ)^50 / (1/200)) + 2 * E^2 * (N : ℝ)^50 :=
      add_le_add (mul_le_mul_of_nonneg_left hmass (Real.exp_pos _).le) htail
    _ = _ := by ring

end RiemannMasullo.Selberg
