module

public import RiemannMasullo.ForMathlib.NumberTheory.LSeries.Selberg.Definitions
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import RiemannMasullo.ForMathlib.NumberTheory.LSeries.Selberg.Arithmetic.TaperSpec
import RiemannMasullo.ForMathlib.NumberTheory.LSeries.Selberg.Fourier.DualEnvelope
import RiemannMasullo.ForMathlib.NumberTheory.LSeries.Selberg.Fourier.DualTransform
import RiemannMasullo.ForMathlib.NumberTheory.LSeries.Selberg.Moments.DualTotal
import RiemannMasullo.ForMathlib.NumberTheory.LSeries.Selberg.Moments.IntervalBessel
import RiemannMasullo.ForMathlib.NumberTheory.LSeries.Selberg.WindowBasic

public section

open MeasureTheory Set

namespace RiemannMasullo.Selberg

private theorem tapered_dual_integrable (N : ℕ) (hN : 2 ≤ N) :
    Integrable (dual N (beta N)) ∧ Integrable (fun y ↦ ‖dual N (beta N) y‖ ^ 2) := by
  obtain ⟨C, hC, henv⟩ := dual_envelope
  obtain ⟨hc, hbound⟩ := henv N hN (beta N) (taper_spec N hN).2
  have hdecay : Integrable (fun y : ℝ ↦ Real.exp (-|y| / 2)) := by
    rw [← integrableOn_univ, ← Iic_union_Ioi (a := (0 : ℝ)), integrableOn_union]
    constructor
    · apply (integrableOn_exp_mul_Iic (by norm_num : 0 < (1/2 : ℝ)) 0).congr_fun
        _ measurableSet_Iic
      intro y hy
      simp only [abs_of_nonpos hy, neg_neg]
      congr 1
      ring
    · apply (integrableOn_exp_mul_Ioi (by norm_num : (-1/2 : ℝ) < 0) 0).congr_fun
        _ measurableSet_Ioi
      intro y hy
      simp only [abs_of_nonneg hy.le]
      congr 1
      ring
  have hi : Integrable (dual N (beta N)) :=
    (hdecay.const_mul (C * (N : ℝ)^53)).mono' hc.aestronglyMeasurable (.of_forall hbound)
  refine ⟨hi, ?_⟩
  simp only [sq]
  apply hi.norm.mul_bdd hc.norm.aestronglyMeasurable (c := C * (N : ℝ)^53)
  refine .of_forall fun y ↦ ?_
  rw [norm_norm]
  have hy : Real.exp (-|y| / 2) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith [abs_nonneg y])
  exact (hbound y).trans (mul_le_of_le_one_right (by positivity) hy)

/-- Card 43. For 0 < h ≤ 1/2 the absolute window second moment on (0,N¹⁰⁰] is bounded by a
constant times h² N⁵⁰.
Titchmarsh, Lemmas 10.18–10.19, pp. 276–277. -/
theorem absolute_second : ∃ A > (0 : ℝ), ∀ N : ℕ, 2 ≤ N → ∀ h : ℝ, 0 < h → h ≤ 1/2 →
    second (H N) (win (fun t ↦ |signal N t|) h) ≤ A*h^2*(N : ℝ)^50 := by
  obtain ⟨C, hC, htotal⟩ := dual_total
  let k : ℝ := 2 * Real.pi ^ (1/4 : ℝ)
  have hk : 0 < k := by dsimp [k]; positivity
  refine ⟨k^2 * (2 * Real.pi * Real.exp 1) * C, by positivity, ?_⟩
  intro N hN h hh _
  have hH : 0 ≤ (H N : ℝ) := Nat.cast_nonneg _
  have hU := add_pos_of_nonneg_of_pos hH hh
  have hcont : Continuous (signal N) :=
    (spectralLineJet_selbergWeight_spec (H N) N (beta N)).1.mul continuous_hardyZ
  have hslide := spectralLineJet_selberg_window_L2 _ hcont.abs hH hh.le
  rw [intervalIntegral.integral_of_le hH, intervalIntegral.integral_of_le hU.le] at hslide
  have hnorm (t : ℝ) : |signal N t|^2 = k^2 * ‖ft (dual N (beta N)) t‖^2 := by
    have he := congrArg norm (dual_transform N hN t)
    change ‖((signal N t : ℝ) : ℂ)‖ = ‖(k : ℂ) * ft (dual N (beta N)) t‖ at he
    simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hk] at he
    rw [he, mul_pow]
  obtain ⟨hi, hi₂⟩ := tapered_dual_integrable N hN
  have henergy := (interval_bessel _ hi hi₂ _ hU).trans
    (mul_le_mul_of_nonneg_left (htotal N hN) (by positivity))
  calc
    _ ≤ h^2 * ∫ t in Ioc (0 : ℝ) (H N + h), |signal N t|^2 := hslide
    _ = h^2 * (k^2 * ∫ t in Ioc (0 : ℝ) (H N + h), ‖ft (dual N (beta N)) t‖^2) := by
      simp_rw [hnorm, integral_const_mul]
    _ ≤ h^2 * (k^2 * (2 * Real.pi * Real.exp 1 * (C * (N : ℝ)^50))) := by gcongr
    _ = _ := by ring

end RiemannMasullo.Selberg
