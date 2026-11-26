module

public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-! # The compensated exponential formula for fractional powers

The formula expresses `(1 + a)^θ - 1` as an integral of positive exponential differences
when `0 < θ < 1` and `a ≥ 0`. It is the scalar input for the heat-kernel representation
of the fractional Sobolev energy in the proposed extension of #7406.

The proof uses the Gamma integral and integration by parts, with both improper boundary
limits verified. The identity itself holds for every `θ < 1`.
-/

@[expose] public noncomputable section
open MeasureTheory Set Filter Real
open scoped Topology
namespace RiemannMasullo

private theorem one_sub_exp_neg_bounds {a t : ℝ} (ha : 0 ≤ a) (ht : 0 ≤ t) :
    0 ≤ 1 - Real.exp (-(a * t)) ∧ 1 - Real.exp (-(a * t)) ≤ a * t := by
  constructor
  · exact sub_nonneg.mpr (Real.exp_le_one_iff.mpr (neg_nonpos.mpr (mul_nonneg ha ht)))
  · linarith [Real.add_one_le_exp (-(a * t))]

private theorem integrableOn_rpow_exp {θ b : ℝ} (hθ : θ < 1) (hb : 0 < b) :
    IntegrableOn (fun t : ℝ ↦ t ^ (-θ) * Real.exp (-(b * t))) (Ioi 0) := by
  simpa only [Real.rpow_one, neg_mul] using
    (integrableOn_rpow_mul_exp_neg_mul_rpow (s := -θ) (p := 1) (by linarith) zero_lt_one hb)

/-- The compensated exponential kernel defining a fractional power is integrable. -/
theorem integrableOn_fractionalPowerKernel {θ a : ℝ} (hθ : θ < 1) (ha : 0 ≤ a) :
    IntegrableOn (fun t : ℝ ↦ Real.exp (-t) * (1 - Real.exp (-(a * t))) *
      t ^ (-1 - θ)) (Ioi 0) := by
  have hi := (integrableOn_rpow_exp (θ := θ) hθ zero_lt_one).const_mul a
  apply hi.mono'
  · exact (by fun_prop : Measurable (fun t : ℝ ↦ Real.exp (-t) *
      (1 - Real.exp (-(a * t))) * t ^ (-1 - θ))).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    change 0 < t at ht
    have hb := one_sub_exp_neg_bounds ha ht.le
    have hp : 0 ≤ t ^ (-1 - θ) := Real.rpow_nonneg ht.le _
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (mul_nonneg (Real.exp_pos _).le hb.1) hp)]
    have hr : t * t ^ (-1 - θ) = t ^ (-θ) := by
      calc
        _ = t ^ (1 : ℝ) * t ^ (-1 - θ) := by rw [Real.rpow_one]
        _ = _ := by rw [← Real.rpow_add ht]; congr 1; ring
    calc
      _ ≤ Real.exp (-t) * (a * t) * t ^ (-1 - θ) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hb.2 (Real.exp_pos _).le) hp
      _ = a * (t ^ (-θ) * Real.exp (-(1 * t))) := by rw [one_mul, ← hr]; ring

/-- The compensated heat-semigroup integral gives the fractional power of `1 + a`. -/
theorem fractionalPower_eq_integral {θ a : ℝ} (hθ : θ < 1) (ha : 0 ≤ a) :
    θ / Real.Gamma (1 - θ) *
      (∫ t : ℝ in Ioi 0, Real.exp (-t) * (1 - Real.exp (-(a * t))) * t ^ (-1 - θ)) =
      (1 + a) ^ θ - 1 := by
  let u (t : ℝ) := t ^ (-θ)
  let v (t : ℝ) := Real.exp (-t) - Real.exp (-((1 + a) * t))
  let du (t : ℝ) := -θ * t ^ (-1 - θ)
  let dv (t : ℝ) := -Real.exp (-t) + (1 + a) * Real.exp (-((1 + a) * t))
  let K (t : ℝ) := Real.exp (-t) * (1 - Real.exp (-(a * t))) * t ^ (-1 - θ)
  have hK : IntegrableOn K (Ioi 0) := integrableOn_fractionalPowerKernel hθ ha
  have hbase : IntegrableOn (fun t : ℝ ↦ t ^ (-θ) * Real.exp (-t)) (Ioi 0) := by
    simpa only [one_mul] using integrableOn_rpow_exp hθ zero_lt_one
  have hother := integrableOn_rpow_exp hθ (show 0 < 1 + a by linarith)
  have hveq (t : ℝ) : v t = Real.exp (-t) * (1 - Real.exp (-(a * t))) := by
    dsimp [v]
    rw [mul_sub, mul_one, ← Real.exp_add]
    congr 2
    ring
  have hu (t : ℝ) (ht : t ∈ Ioi 0) : HasDerivAt u (du t) t := by
    convert (hasDerivAt_id t).rpow_const (p := -θ) (Or.inl ht.ne') using 1 <;>
      first | rfl | (dsimp [u, du]; ring_nf)
  have hv (t : ℝ) (_ht : t ∈ Ioi 0) : HasDerivAt v (dv t) t := by
    convert ((hasDerivAt_id t).neg.exp).sub
      (((hasDerivAt_id t).const_mul (1 + a)).neg.exp) using 1 <;>
      (try funext x) <;> first | rfl | (dsimp [v, dv]; ring_nf)
  have hi1 : IntegrableOn (u * dv) (Ioi 0) := by
    apply (hbase.neg.add (hother.const_mul (1 + a))).congr
    exact .of_forall fun t ↦ by dsimp [u, dv]; ring
  have hi2 : IntegrableOn (du * v) (Ioi 0) := by
    apply (hK.const_mul (-θ)).congr
    exact .of_forall fun t ↦ by dsimp [du, K]; rw [hveq]; ring
  have hb {t : ℝ} (ht : 0 < t) : 0 ≤ (u * v) t ∧
      (u * v) t ≤ a * (t ^ (1 - θ) * Real.exp (-t)) := by
    have hvb := one_sub_exp_neg_bounds ha ht.le
    change 0 ≤ u t * v t ∧ u t * v t ≤ _
    rw [hveq]
    have hp : 0 ≤ u t := Real.rpow_nonneg ht.le _
    constructor
    · exact mul_nonneg hp (mul_nonneg (Real.exp_pos _).le hvb.1)
    · calc
        _ ≤ u t * (Real.exp (-t) * (a * t)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hvb.2 (Real.exp_pos _).le) hp
        _ = _ := by
          have hr : t ^ (-θ) * t = t ^ (1 - θ) := by
            rw [← Real.rpow_add_one ht.ne']
            congr 1
            ring
          dsimp [u]
          calc
            _ = a * ((t ^ (-θ) * t) * Real.exp (-t)) := by ring
            _ = _ := by rw [hr]
  have hzero : Tendsto (u * v) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have hc : Continuous (fun t : ℝ ↦ a * (t ^ (1 - θ) * Real.exp (-t))) :=
      continuous_const.mul ((Real.continuous_rpow_const (by linarith)).mul
        (Real.continuous_exp.comp continuous_id.neg))
    have ht : Tendsto (fun t : ℝ ↦ a * (t ^ (1 - θ) * Real.exp (-t)))
        (𝓝[>] (0 : ℝ)) (𝓝 0) := by
      simpa only [Real.zero_rpow (by linarith : 1 - θ ≠ 0), zero_mul, mul_zero] using
        (hc.tendsto (0 : ℝ)).mono_left (nhdsWithin_le_nhds (s := Ioi 0))
    exact squeeze_zero' (eventually_mem_nhdsWithin.mono fun t ht ↦ (hb ht).1)
      (eventually_mem_nhdsWithin.mono fun t ht ↦ (hb ht).2) ht
  have hinfty : Tendsto (u * v) atTop (𝓝 0) := by
    have ht : Tendsto (fun t : ℝ ↦ a * (t ^ (1 - θ) * Real.exp (-t))) atTop (𝓝 0) := by
      simpa only [one_mul, neg_one_mul, mul_zero] using
        (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (1 - θ) 1 zero_lt_one).const_mul a
    exact squeeze_zero' (eventually_gt_atTop 0 |>.mono fun t ht ↦ (hb ht).1)
      (eventually_gt_atTop 0 |>.mono fun t ht ↦ (hb ht).2) ht
  have hibp := integral_Ioi_mul_deriv_eq_deriv_mul hu hv hi1 hi2 hzero hinfty
  have hid : (∫ t : ℝ in Ioi 0, u t * dv t) =
      -Real.Gamma (1 - θ) + (1 + a) * ((1 / (1 + a)) ^ (1 - θ) * Real.Gamma (1 - θ)) := by
    have he : (fun t ↦ u t * dv t) =
        (fun t ↦ -(t ^ (-θ) * Real.exp (-t))) +
          (fun t ↦ (1 + a) * (t ^ (-θ) * Real.exp (-((1 + a) * t)))) := by
      funext t; dsimp [u, dv]; ring
    rw [he]
    change (∫ t : ℝ in Ioi 0, -(t ^ (-θ) * Real.exp (-t)) +
      (1 + a) * (t ^ (-θ) * Real.exp (-((1 + a) * t)))) = _
    rw [integral_add (f := fun t : ℝ ↦ -(t ^ (-θ) * Real.exp (-t)))
      (g := fun t : ℝ ↦ (1 + a) * (t ^ (-θ) * Real.exp (-((1 + a) * t))))
      hbase.neg (hother.const_mul (1 + a)), integral_neg, integral_const_mul]
    have hg (b : ℝ) (hb : 0 < b) := Real.integral_rpow_mul_exp_neg_mul_Ioi
      (show 0 < 1 - θ by linarith) hb
    simp only [sub_sub_cancel_left] at hg
    have he1 : (∫ t : ℝ in Ioi 0, t ^ (-θ) * Real.exp (-t)) = Real.Gamma (1 - θ) := by
      simpa only [one_mul, one_div_one, Real.one_rpow, one_mul] using hg 1 zero_lt_one
    rw [he1, hg (1 + a) (by linarith)]
  have hik : (∫ t : ℝ in Ioi 0, du t * v t) = -θ * ∫ t : ℝ in Ioi 0, K t := by
    rw [← integral_const_mul]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro t _
    dsimp [du, K]
    rw [hveq]
    ring
  rw [hid, hik, sub_zero, zero_sub] at hibp
  have hpower : (1 + a) * (1 / (1 + a)) ^ (1 - θ) = (1 + a) ^ θ := by
    rw [one_div, Real.inv_rpow (by linarith : 0 ≤ 1 + a), ← Real.rpow_neg (by linarith : 0 ≤ 1 + a)]
    calc
      _ = (1 + a) ^ (1 : ℝ) * (1 + a) ^ (-(1 - θ)) := by rw [Real.rpow_one]
      _ = _ := by rw [← Real.rpow_add (by linarith : 0 < 1 + a)]; congr 1; ring
  have hG : Real.Gamma (1 - θ) ≠ 0 := (Real.Gamma_pos_of_pos (by linarith)).ne'
  change θ / Real.Gamma (1 - θ) * (∫ t : ℝ in Ioi 0, K t) = _
  rw [← mul_assoc, hpower] at hibp
  field_simp [hG]
  nlinarith [hibp]

end RiemannMasullo
