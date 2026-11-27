module

public import RiemannMasullo.ForMathlib.NumberTheory.LSeries.Selberg.Definitions
import RiemannMasullo.ForMathlib.NumberTheory.LSeries.Selberg.Arithmetic.TaperSpec
import RiemannMasullo.ForMathlib.NumberTheory.LSeries.Selberg.Fourier.DualEnvelope
import RiemannMasullo.ForMathlib.NumberTheory.LSeries.Selberg.Fourier.DualTransform
import RiemannMasullo.ForMathlib.NumberTheory.LSeries.Selberg.Moments.DualWindowMass
import RiemannMasullo.ForMathlib.NumberTheory.LSeries.Selberg.Moments.IntervalBessel
import RiemannMasullo.ForMathlib.NumberTheory.LSeries.Selberg.Moments.WindowTransform

public section

open MeasureTheory Set

namespace RiemannMasullo.Selberg

private lemma integrable_envelope_factor : Integrable (fun y : ℝ ↦ Real.exp (-|y| / 2)) := by
  rw [← integrableOn_univ, ← Iic_union_Ioi (a := (0 : ℝ))]
  apply IntegrableOn.union
  · apply (integrableOn_exp_mul_Iic (a := 1/2) (by norm_num) 0).congr_fun _ measurableSet_Iic
    intro y hy
    simp only [abs_of_nonpos hy, neg_neg]
    congr 1
    ring
  · apply (integrableOn_exp_mul_Ioi (a := -(1/2)) (by norm_num) 0).congr_fun _ measurableSet_Ioi
    intro y hy
    simp only [abs_of_pos hy]
    congr 1
    ring

private lemma window_integrability {N : ℕ} (hN : 2 ≤ N) {h : ℝ} (hh : 0 ≤ h) :
    Integrable (dual N (beta N)) ∧
    Integrable (fun y ↦ dual N (beta N) y * mult h y) ∧
    Integrable (fun y ↦ ‖dual N (beta N) y * mult h y‖ ^ 2) := by
  obtain ⟨D, hD, henv⟩ := dual_envelope
  obtain ⟨hcont, hbound⟩ := henv N hN (beta N) (taper_spec N hN).2
  have hf := (integrable_envelope_factor.const_mul (D * (N : ℝ)^53)).mono'
    hcont.aestronglyMeasurable (.of_forall hbound)
  have hm : Continuous (mult h) := by
    unfold mult
    apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    unfold Function.uncurry osc
    fun_prop
  have hlen (y : ℝ) : ‖mult h y‖ ≤ h := by
    simpa only [mult, osc, sub_zero, abs_of_nonneg hh, one_mul] using
      (intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := h)
        (fun u _ ↦ (Complex.norm_exp_I_mul_ofReal (u * y)).le))
  have hprod := hf.mul_bdd hm.aestronglyMeasurable (.of_forall hlen)
  refine ⟨hf, hprod, ?_⟩
  simp_rw [sq]
  apply hprod.norm.mul_bdd hprod.norm.aestronglyMeasurable (c := D * (N : ℝ)^53 * h)
  refine .of_forall fun y ↦ ?_
  rw [Real.norm_of_nonneg (norm_nonneg _), norm_mul]
  apply mul_le_mul _ (hlen y) (norm_nonneg _) (by positivity)
  exact (hbound y).trans (mul_le_of_le_one_right (by positivity)
    (Real.exp_le_one_iff.mpr (div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (abs_nonneg _))
      zero_le_two)))

/-- Card 42. For 0 < h ≤ 1/2 the signed window second moment on (0,N¹⁰⁰] is bounded by a constant
times h N⁵⁰/log N.
Titchmarsh, (10.17.1), p. 275. -/
theorem signed_second : ∃ B > (0 : ℝ), ∀ N : ℕ, 2 ≤ N → ∀ h : ℝ, 0 < h → h ≤ 1/2 →
    second (H N) (win (signal N) h) ≤ B*h*(N : ℝ)^50/Real.log N := by
  obtain ⟨C, hC, hmass⟩ := dual_window_mass
  let k := 2 * Real.pi ^ (1/4 : ℝ)
  have hk : 0 < k := by dsimp [k]; positivity
  refine ⟨k^2 * (2 * Real.pi * Real.exp 1) * C, by positivity, ?_⟩
  intro N hN h hh hhalf
  let F := fun y ↦ dual N (beta N) y * mult h y
  obtain ⟨hint, hF, hF₂⟩ := window_integrability hN hh.le
  have hwin (t : ℝ) : (win (signal N) h t : ℂ) = (k : ℂ) * ft F t := by
    rw [win, ← intervalIntegral.integral_ofReal]
    simp_rw [dual_transform N hN]
    rw [intervalIntegral.integral_const_mul, window_transform _ hint h t hh.le]
  have hsq (t : ℝ) : (win (signal N) h t)^2 = k^2 * ‖ft F t‖^2 := by
    calc
      _ = ‖(win (signal N) h t : ℂ)‖^2 := by rw [Complex.norm_real, Real.norm_eq_abs, sq_abs]
      _ = _ := by rw [hwin, norm_mul, mul_pow, Complex.norm_real, Real.norm_of_nonneg hk.le]
  have hU : 0 < (H N : ℝ) := by
    exact_mod_cast (pow_pos (by omega : 0 < N) 100)
  calc
    second (H N) (win (signal N) h) = k^2 * ∫ t in Ioc (0 : ℝ) (H N), ‖ft F t‖^2 := by
      simp only [second, hsq, integral_const_mul]
    _ ≤ k^2 * (2 * Real.pi * Real.exp 1 * ∫ y : ℝ, ‖F y‖^2) :=
      mul_le_mul_of_nonneg_left (interval_bessel F hF hF₂ _ hU) (sq_nonneg k)
    _ ≤ k^2 * (2 * Real.pi * Real.exp 1 * (C*h*(N : ℝ)^50/Real.log N)) := by
      gcongr
      exact hmass N hN h hh hhalf
    _ = _ := by ring

end RiemannMasullo.Selberg
