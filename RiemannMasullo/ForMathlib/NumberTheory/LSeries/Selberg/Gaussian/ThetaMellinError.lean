module

public import RiemannMasullo.ForMathlib.NumberTheory.LSeries.Selberg.Definitions
import RiemannMasullo.ForMathlib.NumberTheory.LSeries.Selberg.Gaussian.ThetaError

public section

open MeasureTheory Set

namespace RiemannMasullo.Selberg

private noncomputable def weightedError (q z x : ℝ) : ℝ :=
  x ^ (-q) * (theta (z * x) - gaussC / (z * x))

private lemma measurable_weightedError (q z : ℝ) : Measurable (weightedError q z) := by
  unfold weightedError theta
  fun_prop

private lemma abs_weightedError_le (q : ℝ) {z x : ℝ} (hz : 0 < z) (hx : 0 < x) :
    |weightedError q z x| ≤ x ^ (-q) * min 1 (gaussC / (z * x)) := by
  obtain ⟨hpos, hbound⟩ := theta_error (z * x) (mul_pos hz hx)
  rw [weightedError, abs_mul, abs_of_nonneg (Real.rpow_nonneg hx.le _),
    abs_sub_comm, abs_of_nonneg hpos]
  exact mul_le_mul_of_nonneg_left hbound (Real.rpow_nonneg hx.le _)

private lemma integral_weightedError (q : ℝ) {z : ℝ} (hz : 0 < z) :
    ∫ x in Ioi 0, weightedError q z x = z ^ (q - 1) * errorC q := by
  let f := fun v : ℝ ↦ v ^ (-q) * (theta v - gaussC / v)
  calc
    _ = ∫ x in Ioi 0, z ^ q * f (z * x) := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro x hx
      dsimp [weightedError, f]
      rw [Real.mul_rpow hz.le (le_of_lt hx), Real.rpow_neg hz.le]
      field_simp [ne_of_gt (Real.rpow_pos_of_pos hz q)]
    _ = z ^ (q - 1) * errorC q := by
      rw [integral_const_mul, integral_comp_mul_left_Ioi f 0 hz, mul_zero,
        smul_eq_mul, Real.rpow_sub_one hz.ne']
      change z ^ q * (z⁻¹ * errorC q) = z ^ q / z * errorC q
      ring

/-- Card 24. For 0 < q ≤ 1/2 and z > 0 the weighted theta integral differs from `gaussC/(q*z) +
z^(q-1)*errorC q` by at most two. The coefficient `errorC q` is nonpositive.
Replacement for Titchmarsh (10.11.1), pp. 270–271, x=1. -/
theorem theta_mellin_error (q z : ℝ) (hq : 0 < q) (hq' : q ≤ 1/2) (hz : 0 < z) :
    errorC q ≤ 0 ∧
    |(∫ x in Ioi (1 : ℝ), x^(-q)*theta (z*x)) -
      (gaussC/(q*z) + z^(q-1)*errorC q)| ≤ 2 := by
  constructor
  · apply setIntegral_nonpos measurableSet_Ioi
    intro v hv
    exact mul_nonpos_of_nonneg_of_nonpos (Real.rpow_nonneg (le_of_lt hv) _)
      (sub_nonpos.mpr (sub_nonneg.mp (theta_error v hv).1))
  have hnear : -1 < -q := by linarith
  have hfar : -q - 1 < -1 := by linarith
  -- On the tail the Gaussian integral approximation also dominates the absolute error.
  let main := fun x : ℝ ↦ gaussC / z * x ^ (-q - 1)
  have hmain_eq (x : ℝ) (hx : 0 < x) :
      x ^ (-q) * (gaussC / (z * x)) = main x := by
    dsimp [main]
    rw [Real.rpow_sub_one hx.ne']
    ring
  have hmain : IntegrableOn main (Ioi 1) :=
    (integrableOn_Ioi_rpow_of_lt hfar zero_lt_one).const_mul _
  have hmain_int : ∫ x in Ioi 1, main x = gaussC / (q * z) := by
    dsimp [main]
    rw [integral_const_mul, integral_Ioi_rpow_of_lt hfar zero_lt_one, Real.one_rpow,
      sub_add_cancel, neg_div_neg_eq]
    ring
  have htail : IntegrableOn (weightedError q z) (Ioi 1) := by
    apply hmain.mono' (measurable_weightedError q z).aestronglyMeasurable
    filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Ioi] with x hx
    have hx' : 0 < x := zero_lt_one.trans hx
    rw [Real.norm_eq_abs, ← hmain_eq x hx']
    exact (abs_weightedError_le q hz hx').trans
      (mul_le_mul_of_nonneg_left (min_le_right ..) (Real.rpow_nonneg hx'.le _))
  have htheta_int : (∫ x in Ioi (1 : ℝ), x ^ (-q) * theta (z * x)) =
      gaussC / (q * z) + ∫ x in Ioi 1, weightedError q z x := by
    rw [← hmain_int, ← integral_add hmain htail]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro x hx
    dsimp only
    rw [← hmain_eq x (zero_lt_one.trans hx), weightedError]
    ring
  -- On (0, 1] the unit mesh-error bound is independent of the scale z.
  have hpower : IntegrableOn (fun x : ℝ ↦ x ^ (-q)) (Ioc 0 1) :=
    (intervalIntegral.intervalIntegrable_rpow' hnear).1
  have hbound : ∀ᵐ x ∂volume.restrict (Ioc 0 1), ‖weightedError q z x‖ ≤ x ^ (-q) := by
    filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Ioc] with x hx
    rw [Real.norm_eq_abs]
    exact (abs_weightedError_le q hz hx.1).trans
      (by simpa using mul_le_mul_of_nonneg_left (min_le_left 1 (gaussC / (z * x)))
            (Real.rpow_nonneg hx.1.le (-q)))
  have hhead : IntegrableOn (weightedError q z) (Ioc 0 1) :=
    hpower.mono' (measurable_weightedError q z).aestronglyMeasurable hbound
  have hsplit := setIntegral_union Ioc_disjoint_Ioi_same measurableSet_Ioi hhead htail
  rw [Ioc_union_Ioi_eq_Ioi zero_le_one, integral_weightedError q hz] at hsplit
  rw [htheta_int, hsplit, add_sub_add_left_eq_sub, abs_sub_comm, add_sub_cancel_right,
    ← Real.norm_eq_abs]
  calc
    _ ≤ ∫ x in Ioc (0 : ℝ) 1, x ^ (-q) := norm_integral_le_of_norm_le hpower hbound
    _ = 1 / (-q + 1) := by
      rw [← intervalIntegral.integral_of_le zero_le_one, integral_rpow (.inl hnear),
        Real.one_rpow, Real.zero_rpow (by linarith : -q + 1 ≠ 0), sub_zero]
    _ ≤ 2 := (div_le_iff₀ (by linarith)).mpr (by linarith)

end RiemannMasullo.Selberg
