module

public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-! # Laplace representation of a shifted fractional power -/

public section

open MeasureTheory Set
open scoped ENNReal Interval

namespace RiemannMasullo

private theorem lintegral_mul_exp_neg_mul_interval {u a : ℝ} (hu : 0 < u) (ha : 0 ≤ a) :
    (∫⁻ r in Ioc 0 a, ENNReal.ofReal (u * Real.exp (-(u * r)))) =
      ENNReal.ofReal (1 - Real.exp (-(u * a))) := by
  have hc : Continuous (fun r ↦ u * Real.exp (-(u * r))) := by fun_prop
  have hi := (hc.intervalIntegrable (μ := volume) 0 a).1
  rw [← ofReal_integral_eq_lintegral_ofReal hi (ae_of_all _ fun _ ↦ by positivity),
    ← intervalIntegral.integral_of_le ha]
  have hd (r : ℝ) : HasDerivAt (fun r ↦ -Real.exp (-(u * r)))
      (u * Real.exp (-(u * r))) r := by
    convert ((Real.hasDerivAt_exp (-(u * r))).comp r
      (((hasDerivAt_id r).const_mul u).neg)).neg using 1 <;> first | rfl | ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun r _ ↦ hd r)
    (hc.intervalIntegrable _ _)]
  simp [sub_eq_add_neg, add_comm]

private theorem rpow_neg_sub_one_mul {u s : ℝ} (hu : 0 < u) :
    u ^ (-s - 1) * u = u ^ (-s) := by
  nth_rw 2 [← Real.rpow_one u]
  rw [← Real.rpow_add hu]
  congr 1
  ring

private theorem lintegral_gammaLaplace {s r : ℝ} (hs : s < 1) (hr : 0 ≤ r) :
    (∫⁻ u in Ioi (0 : ℝ), ENNReal.ofReal (u ^ (-s) * Real.exp (-(1 + r) * u))) =
      ENNReal.ofReal ((1 + r) ^ (s - 1) * Real.Gamma (1 - s)) := by
  have hR : 0 < 1 + r := by linarith
  have hs' : -1 < -s := by linarith
  have hi : IntegrableOn (fun u : ℝ ↦ u ^ (-s) * Real.exp (-(1 + r) * u)) (Ioi 0) := by
    simpa only [Real.rpow_one, neg_mul] using
      (integrableOn_rpow_mul_exp_neg_mul_rpow hs' (p := 1) (by norm_num) hR)
  rw [← ofReal_integral_eq_lintegral_ofReal hi
    ((ae_restrict_mem measurableSet_Ioi).mono fun u hu ↦
      mul_nonneg (Real.rpow_nonneg hu.le _) (Real.exp_pos _).le)]
  have hp : (1 / (1 + r)) ^ (1 - s) = (1 + r) ^ (s - 1) := by
    rw [one_div, Real.inv_rpow hR.le, ← Real.rpow_neg hR.le]
    congr 1
    ring
  have he := Real.integral_rpow_mul_exp_neg_mul_Ioi (sub_pos.mpr hs) hR
  rw [show 1 - s - 1 = -s by ring, hp] at he
  simpa only [neg_mul] using congrArg ENNReal.ofReal he

/-- The shifted fractional power ( (1+a)^s-1 ) is an integral of the Laplace
differences (1-e^{-ua}) against the tempered jump density. -/
theorem lintegral_tempered_laplace_difference {s a : ℝ}
    (hs : 0 < s) (hs' : s < 1) (ha : 0 ≤ a) :
    (∫⁻ u in Ioi (0 : ℝ), ENNReal.ofReal
      ((s / Real.Gamma (1 - s) * Real.exp (-u) * u ^ (-s - 1)) *
        (1 - Real.exp (-(u * a))))) = ENNReal.ofReal ((1 + a) ^ s - 1) := by
  let U : Measure ℝ := volume.restrict (Ioi 0)
  let V : Measure ℝ := volume.restrict (Ioc 0 a)
  let c := s / Real.Gamma (1 - s)
  let w (u : ℝ) := c * Real.exp (-u) * u ^ (-s - 1)
  let k (u r : ℝ) := ENNReal.ofReal (c * (u ^ (-s) * Real.exp (-(1 + r) * u)))
  have hG : 0 < Real.Gamma (1 - s) := Real.Gamma_pos_of_pos (sub_pos.mpr hs')
  have hc : 0 ≤ c := div_nonneg hs.le hG.le
  have hk : Measurable (Function.uncurry k) := by
    dsimp [Function.uncurry, k]
    fun_prop
  change (∫⁻ u, ENNReal.ofReal (w u * (1 - Real.exp (-(u * a)))) ∂U) = _
  calc
    _ = ∫⁻ u, (∫⁻ r, k u r ∂V) ∂U := by
      apply lintegral_congr_ae
      filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Ioi] with u hu
      have hu' : 0 < u := hu
      have hw : 0 ≤ w u := by dsimp [w]; positivity
      rw [ENNReal.ofReal_mul hw, ← lintegral_mul_exp_neg_mul_interval hu' ha,
        ← lintegral_const_mul _ (by fun_prop)]
      refine lintegral_congr fun r ↦ ?_
      rw [← ENNReal.ofReal_mul hw]
      congr 1
      dsimp [w, k]
      rw [show -(1 + r) * u = -u + -(u * r) by ring, Real.exp_add, ← rpow_neg_sub_one_mul hu']
      ring
    _ = ∫⁻ r, (∫⁻ u, k u r ∂U) ∂V := lintegral_lintegral_swap hk.aemeasurable
    _ = ∫⁻ r, ENNReal.ofReal (s * (1 + r) ^ (s - 1)) ∂V := by
      apply lintegral_congr_ae
      filter_upwards [ae_restrict_mem (μ := volume) (measurableSet_Ioc (a := (0 : ℝ)) (b := a))]
        with r hr
      have hr' : 0 ≤ r := hr.1.le
      dsimp [k]
      simp_rw [ENNReal.ofReal_mul hc]
      rw [lintegral_const_mul _ (by fun_prop), lintegral_gammaLaplace hs' hr',
        ← ENNReal.ofReal_mul hc]
      congr 1
      dsimp [c]
      field_simp
    _ = _ := by
      have hd (r : ℝ) (hr : r ∈ [[(0 : ℝ), a]]) :
          HasDerivAt (fun r ↦ (1 + r) ^ s) (s * (1 + r) ^ (s - 1)) r := by
        rw [uIcc_of_le ha] at hr
        have hne : 1 + r ≠ 0 := by linarith [hr.1]
        simpa only [Function.comp_def, id_eq, mul_one, Pi.add_apply] using
          (Real.hasDerivAt_rpow_const (Or.inl hne)).comp r ((hasDerivAt_id r).const_add 1)
      have hcont : ContinuousOn (fun r ↦ s * (1 + r) ^ (s - 1)) [[(0 : ℝ), a]] := by
        rw [uIcc_of_le ha]
        refine continuousOn_const.mul ((continuous_const.add continuous_id).continuousOn.rpow_const ?_)
        intro r hr
        apply Or.inl
        change 1 + r ≠ 0
        linarith [hr.1]
      have hi := hcont.intervalIntegrable (μ := volume)
      rw [← ofReal_integral_eq_lintegral_ofReal hi.1
        ((ae_restrict_mem measurableSet_Ioc).mono fun r hr ↦
          mul_nonneg hs.le (Real.rpow_nonneg (by linarith [hr.1]) _)),
        ← intervalIntegral.integral_of_le ha, intervalIntegral.integral_eq_sub_of_hasDerivAt hd hi]
      simp

/-- The tempered fractional weight integrated against (2u) gives (2s). -/
theorem lintegral_tempered_laplace_mul_twice {s : ℝ} (hs : 0 < s) (hs' : s < 1) :
    (∫⁻ u in Ioi (0 : ℝ), ENNReal.ofReal
      ((s / Real.Gamma (1 - s) * Real.exp (-u) * u ^ (-s - 1)) * (2 * u))) =
    ENNReal.ofReal (2 * s) := by
  let c := 2 * (s / Real.Gamma (1 - s))
  have hG : 0 < Real.Gamma (1 - s) := Real.Gamma_pos_of_pos (sub_pos.mpr hs')
  have hc : 0 ≤ c := by dsimp [c]; positivity
  calc
    _ = ∫⁻ u in Ioi (0 : ℝ), ENNReal.ofReal c *
        ENNReal.ofReal (u ^ (-s) * Real.exp (-(1 + 0) * u)) := by
      apply lintegral_congr_ae
      filter_upwards [ae_restrict_mem (μ := volume) (measurableSet_Ioi (a := (0 : ℝ)))] with u hu
      have hu' : 0 < u := hu
      rw [← ENNReal.ofReal_mul hc]
      congr 1
      rw [add_zero, neg_one_mul, ← rpow_neg_sub_one_mul hu']
      dsimp [c]
      ring
    _ = _ := by
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_gammaLaplace hs' le_rfl]
      simp only [add_zero, Real.one_rpow, one_mul, ← ENNReal.ofReal_mul hc]
      congr 1
      dsimp [c]
      field_simp

end RiemannMasullo
