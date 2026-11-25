module

public import Mathlib.Analysis.Calculus.ContDiff.Deriv
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
import Mathlib.Tactic

/-! # An explicit centered cutoff for weak cardinal localization -/

open Set MeasureTheory Filter
open scoped Topology ContDiff Interval

@[expose] public noncomputable section

namespace RiemannMasullo.WeakCardinal

/-- The compact cutoff used to preserve the cardinal values on the local window. -/
def cutoffEta (y : ℝ) : ℝ := if |y| ≤ 1 then (1 - y ^ 2) ^ 2 else 0

/-- The continuous extension of the cutoff complement divided by its argument. -/
def cutoffQuotient (y : ℝ) : ℝ := if |y| ≤ 1 then 2*y - y^3 else y⁻¹

/-- The derivative, with the same value from either side at both endpoints. -/
def cutoffQuotientPrime (y : ℝ) : ℝ := if |y| ≤ 1 then 2-3*y^2 else -(y⁻¹)^2

/-- A representative of the weak second derivative. -/
def cutoffQuotientSecond (y : ℝ) : ℝ := if |y| ≤ 1 then -6*y else 2*(y⁻¹)^3

theorem cutoffQuotient_mul (y : ℝ) : cutoffQuotient y * y = 1-cutoffEta y := by
  by_cases h : |y| ≤ 1
  · simp only [cutoffQuotient, cutoffEta, ite_eq_left h]; ring
  · have hy : y ≠ 0 := fun he ↦ h (by simp [he])
    simp [cutoffQuotient, cutoffEta, h, hy]

private theorem outer_value {y : ℝ} (h : 1 ≤ |y|) : cutoffQuotient y = y⁻¹ := by
  rcases h.eq_or_lt with he | hl
  · rcases (abs_eq (by norm_num : (0:ℝ) ≤ 1)).mp he.symm with rfl | rfl <;> norm_num [cutoffQuotient]
  · simp [cutoffQuotient, hl.not_ge]

private theorem outer_prime {y : ℝ} (h : 1 ≤ |y|) : cutoffQuotientPrime y = -(y⁻¹)^2 := by
  rcases h.eq_or_lt with he | hl
  · rcases (abs_eq (by norm_num : (0:ℝ) ≤ 1)).mp he.symm with rfl | rfl <;> norm_num [cutoffQuotientPrime]
  · simp [cutoffQuotientPrime, hl.not_ge]

private theorem poly_hasDerivAt (x : ℝ) :
    HasDerivAt (fun t : ℝ ↦ 2*t - t^3) (2-3*x^2) x := by
  convert ((hasDerivAt_id x).const_mul 2).sub ((hasDerivAt_id x).pow 3) using 1
  · rfl
  · norm_num

private theorem inv_hasDerivAt' {x : ℝ} (hx : x ≠ 0) :
    HasDerivAt (fun t : ℝ ↦ t⁻¹) (-(x⁻¹)^2) x := by
  simpa only [inv_pow] using hasDerivAt_inv hx

/-- The quotient is differentiable through both cutoff endpoints. -/
theorem hasDerivAt_cutoffQuotient (x : ℝ) :
    HasDerivAt cutoffQuotient (cutoffQuotientPrime x) x := by
  rcases lt_trichotomy |x| 1 with hi | he | ho
  · rw [cutoffQuotientPrime, ite_eq_left hi.le]
    apply (poly_hasDerivAt x).congr_of_eventuallyEq
    filter_upwards [continuous_abs.continuousAt.eventually_lt_const hi] with t ht
    simp [cutoffQuotient, ht.le]
  · let S := {t : ℝ | |t| ≤ 1}
    let T := {t : ℝ | 1 ≤ |t|}
    have hunion : S ∪ T = univ := eq_univ_iff_forall.mpr fun t ↦ le_total |t| 1
    have hx : x ≠ 0 := fun h ↦ by simp [h] at he
    have hin : HasDerivWithinAt cutoffQuotient (cutoffQuotientPrime x) S x := by
      rw [cutoffQuotientPrime, ite_eq_left he.le]
      exact (poly_hasDerivAt x).hasDerivWithinAt.congr
        (fun _ ht ↦ ite_eq_left ht) (ite_eq_left he.le)
    have hout : HasDerivWithinAt cutoffQuotient (cutoffQuotientPrime x) T x := by
      rw [outer_prime he.ge]
      exact (inv_hasDerivAt' hx).hasDerivWithinAt.congr (fun _ ht ↦ outer_value ht) (outer_value he.ge)
    simpa only [hunion, hasDerivWithinAt_univ] using hin.union hout
  · rw [outer_prime ho.le]
    have hx : x ≠ 0 := fun h ↦ by norm_num [h] at ho
    apply (inv_hasDerivAt' hx).congr_of_eventuallyEq
    filter_upwards [continuous_abs.continuousAt.eventually_const_lt ho] with t ht
    exact outer_value ht.le

theorem continuous_cutoffQuotientPrime : Continuous cutoffQuotientPrime := by
  have he : cutoffQuotientPrime = fun x : ℝ ↦ (2-3*min (x^2) 1)/max (x^2) 1 := by
    funext x
    by_cases hx : |x| ≤ 1
    · have hsq : x^2 ≤ 1 := by nlinarith [sq_abs x, mul_self_le_mul_self (abs_nonneg x) hx]
      rw [cutoffQuotientPrime, ite_eq_left hx, min_eq_left hsq, max_eq_right hsq, div_one]
    · have hsq : 1 ≤ x^2 := by nlinarith [sq_abs x, mul_self_le_mul_self (by norm_num : (0:ℝ) ≤ 1) (le_of_not_ge hx)]
      rw [cutoffQuotientPrime, ite_eq_right hx, min_eq_right hsq, max_eq_left hsq, div_eq_mul_inv, inv_pow]
      ring
  rw [he]
  exact (continuous_const.sub (continuous_const.mul ((continuous_pow 2).min continuous_const))).div
    ((continuous_pow 2).max continuous_const) (fun x ↦ (zero_lt_one.trans_le (le_max_right (x^2) 1)).ne')

theorem contDiff_cutoffQuotient : ContDiff ℝ 1 cutoffQuotient := by
  apply contDiff_one_iff_deriv.mpr
  exact ⟨fun x ↦ (hasDerivAt_cutoffQuotient x).differentiableAt,
    (funext fun x ↦ (hasDerivAt_cutoffQuotient x).deriv) ▸ continuous_cutoffQuotientPrime⟩

theorem contDiff_cutoffEta : ContDiff ℝ 1 cutoffEta := by
  have h : cutoffEta = fun x : ℝ ↦ 1-cutoffQuotient x*x := funext fun x ↦ by linarith [cutoffQuotient_mul x]
  rw [h]
  exact contDiff_const.sub (contDiff_cutoffQuotient.mul contDiff_id)

private theorem hasDerivAt_prime_of_abs_ne_one {y : ℝ} (hy : |y| ≠ 1) :
    HasDerivAt cutoffQuotientPrime (cutoffQuotientSecond y) y := by
  rcases lt_or_gt_of_ne hy with hi | ho
  · rw [cutoffQuotientSecond, ite_eq_left hi.le]
    have hd : HasDerivAt (fun x : ℝ ↦ 2-3*x^2) (-6*y) y := by
      convert (hasDerivAt_const y (2:ℝ)).sub (((hasDerivAt_id y).pow 2).const_mul 3) using 1
      · rfl
      · simp; ring
    apply hd.congr_of_eventuallyEq
    filter_upwards [continuous_abs.continuousAt.eventually_lt_const hi] with x hx
    exact ite_eq_left hx.le
  · rw [cutoffQuotientSecond, ite_eq_right ho.not_ge]
    have h0 : y ≠ 0 := fun h ↦ by norm_num [h] at ho
    have hd : HasDerivAt (fun x : ℝ ↦ -(x⁻¹)^2) (2*(y⁻¹)^3) y := by
      convert ((inv_hasDerivAt' h0).pow 2).neg using 1; simp; ring
    apply hd.congr_of_eventuallyEq
    filter_upwards [continuous_abs.continuousAt.eventually_const_lt ho] with x hx
    exact outer_prime hx.le

/-- Off the two endpoints the classical derivative of the first derivative is the
stated weak second derivative. -/
theorem ae_hasDerivAt_cutoffQuotientPrime : ∀ᵐ y : ℝ,
    HasDerivAt cutoffQuotientPrime (cutoffQuotientSecond y) y := by
  filter_upwards [(volume : Measure ℝ).ae_ne 1, (volume : Measure ℝ).ae_ne (-1)] with y hp hn
  exact hasDerivAt_prime_of_abs_ne_one fun he ↦
    ((abs_eq (by norm_num : (0:ℝ) ≤ 1)).mp he).elim hp hn

private theorem abs_inv_le_one_of_outer {x : ℝ} (hx : 1 ≤ |x|) : |x⁻¹| ≤ 1 := by
  rw [abs_inv, ← one_div]
  exact (one_div_le_one_div_of_le zero_lt_one hx).trans_eq (by norm_num)

theorem abs_cutoffQuotient_le (x : ℝ) : |cutoffQuotient x| ≤ 9/8 := by
  by_cases hx : |x| ≤ 1
  · have hs : x^2 ≤ 1 := by nlinarith [sq_abs x, mul_self_le_mul_self (abs_nonneg x) hx]
    rw [cutoffQuotient, ite_eq_left hx, show 2*x-x^3 = x*(2-x^2) by ring, abs_mul,
      abs_of_nonneg (by linarith : 0 ≤ 2-x^2), ← sq_abs x]
    nlinarith [mul_nonneg (sq_nonneg (|x| - 4/5)) (show 0 ≤ |x| + 8/5 by positivity)]
  · rw [outer_value (le_of_not_ge hx)]
    exact (abs_inv_le_one_of_outer (le_of_not_ge hx)).trans (by norm_num)

theorem abs_cutoffQuotientPrime_le (x : ℝ) : |cutoffQuotientPrime x| ≤ 2 := by
  by_cases hx : |x| ≤ 1
  · rw [cutoffQuotientPrime, ite_eq_left hx, abs_le]
    have hs : x^2 ≤ 1 := by nlinarith [sq_abs x, mul_self_le_mul_self (abs_nonneg x) hx]
    constructor <;> nlinarith [sq_nonneg x]
  · rw [outer_prime (le_of_not_ge hx), abs_neg, abs_pow]
    have h := abs_inv_le_one_of_outer (le_of_not_ge hx)
    nlinarith [mul_self_le_mul_self (abs_nonneg x⁻¹) h]

theorem abs_cutoffQuotientSecond_le (x : ℝ) : |cutoffQuotientSecond x| ≤ 6 := by
  by_cases hx : |x| ≤ 1
  · rw [cutoffQuotientSecond, ite_eq_left hx, abs_mul]
    norm_num
    linarith
  · rw [cutoffQuotientSecond, ite_eq_right hx, abs_mul, abs_pow]
    have h : |x⁻¹|^3 ≤ 1 := pow_le_one₀ (abs_nonneg x⁻¹) (abs_inv_le_one_of_outer (le_of_not_ge hx))
    rw [abs_of_pos (by norm_num : (0:ℝ) < 2)]
    linarith

/-- The centered and scaled coefficient multiplying the centered moment. -/
def scaledCutoffQuotient (w R x : ℝ) : ℝ := cutoffQuotient ((x-w)/R)/R

theorem scaledCutoffQuotient_mul_sub (w R x : ℝ) :
    scaledCutoffQuotient w R x * (x-w) = 1-cutoffEta ((x-w)/R) := by
  rw [← cutoffQuotient_mul]
  unfold scaledCutoffQuotient
  ring

theorem scaledCutoffQuotient_mul_sub_of_le_abs {w R x : ℝ} (hR : 0 < R) (hx : R ≤ |x-w|) :
    scaledCutoffQuotient w R x * (x-w) = 1 := by
  have hy : 1 ≤ |(x-w)/R| := by rwa [abs_div, abs_of_pos hR, le_div_iff₀ hR, one_mul]
  rw [scaledCutoffQuotient_mul_sub]
  rcases hy.eq_or_lt with he | ho
  · have hs : ((x-w)/R)^2 = 1 := by nlinarith [sq_abs ((x-w)/R)]
    simp [cutoffEta, he.symm, hs]
  · simp [cutoffEta, ho.not_ge]

theorem scaledCutoffQuotient_value_bound {R : ℝ} (hR : 0 < R) (w x : ℝ) :
    |scaledCutoffQuotient w R x| ≤ (9/8)/R := by
  rw [scaledCutoffQuotient, abs_div, abs_of_pos hR]
  exact div_le_div_of_nonneg_right (abs_cutoffQuotient_le _) hR.le

theorem hasDerivAt_scaledCutoffQuotient (w R x : ℝ) :
    HasDerivAt (scaledCutoffQuotient w R) (cutoffQuotientPrime ((x-w)/R)/R^2) x := by
  have ht : HasDerivAt (fun t : ℝ ↦ (t-w)/R) (1/R) x := ((hasDerivAt_id x).sub_const w).div_const R
  convert ((hasDerivAt_cutoffQuotient _).comp x ht).div_const R using 1
  · rfl
  · ring

theorem ae_hasDerivAt_scaledCutoffQuotientPrime (w : ℝ) {R : ℝ} (hR : 0 < R) :
    ∀ᵐ x : ℝ, HasDerivAt (fun t ↦ cutoffQuotientPrime ((t-w)/R)/R^2)
      (cutoffQuotientSecond ((x-w)/R)/R^3) x := by
  filter_upwards [(volume : Measure ℝ).ae_ne (w+R), (volume : Measure ℝ).ae_ne (w-R)] with x hp hn
  have hy : |(x-w)/R| ≠ 1 := by
    intro he
    rcases (abs_eq (by norm_num : (0:ℝ) ≤ 1)).mp he with H | H
    · exact hp (by linarith [(div_eq_iff hR.ne').mp H])
    · exact hn (by linarith [(div_eq_iff hR.ne').mp H])
  have ht : HasDerivAt (fun t : ℝ ↦ (t-w)/R) (1/R) x := ((hasDerivAt_id x).sub_const w).div_const R
  convert ((hasDerivAt_prime_of_abs_ne_one hy).comp x ht).div_const (R^2) using 1
  · rfl
  · ring

/-- The multiplier constant for the graph norm of `1-∂²` at radius six. -/
theorem radius_six_multiplier_constant :
    (9/8 : ℝ)/6 + 2/6^2 + 6/6^3 = 13/48 := by norm_num

private theorem rightDeriv_prime (x : ℝ) : ∃ d : ℝ, ‖d‖ ≤ 6 ∧
    HasDerivWithinAt cutoffQuotientPrime d (Ici x) x := by
  by_cases hx : |x| = 1
  · rcases (abs_eq (by norm_num : (0:ℝ) ≤ 1)).mp hx with rfl | rfl
    · refine ⟨2, by norm_num, ?_⟩
      have hd : HasDerivAt (fun t : ℝ ↦ -(t⁻¹)^2) 2 1 := by
        convert ((inv_hasDerivAt' (one_ne_zero : (1:ℝ) ≠ 0)).pow 2).neg using 1; norm_num
      exact hd.hasDerivWithinAt.congr_of_mem (fun t ht ↦ outer_prime (ht.trans (le_abs_self t))) le_rfl
    · refine ⟨6, by norm_num, ?_⟩
      have hd : HasDerivAt (fun t : ℝ ↦ 2-3*t^2) 6 (-1) := by
        convert (hasDerivAt_const (-1:ℝ) (2:ℝ)).sub (((hasDerivAt_id (-1:ℝ)).pow 2).const_mul 3) using 1
        · rfl
        · norm_num
      apply hd.hasDerivWithinAt.congr_of_eventuallyEq _ (by norm_num [cutoffQuotientPrime])
      filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds
        (Iio_mem_nhds (by norm_num : (-1 : ℝ) < 1))] with t ht ht'
      exact ite_eq_left (abs_le.mpr ⟨ht, le_of_lt ht'⟩)
  · exact ⟨_, abs_cutoffQuotientSecond_le x, (hasDerivAt_prime_of_abs_ne_one hx).hasDerivWithinAt⟩

/-- The derivative is globally Lipschitz, including across the two gluing points. -/
theorem lipschitzWith_cutoffQuotientPrime : LipschitzWith 6 cutoffQuotientPrime := by
  choose d hd hder using rightDeriv_prime
  have hb {a b : ℝ} (hab : a ≤ b) : ‖cutoffQuotientPrime b-cutoffQuotientPrime a‖ ≤ 6*(b-a) :=
    norm_image_sub_le_of_norm_deriv_right_le_segment continuous_cutoffQuotientPrime.continuousOn
      (fun x _ ↦ hder x) (fun x _ ↦ hd x) b ⟨hab, le_rfl⟩
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rcases le_total y x with h | h
  · simpa only [dist_eq_norm, Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr h), NNReal.coe_ofNat] using hb h
  · rw [dist_comm x y, dist_comm (cutoffQuotientPrime x) (cutoffQuotientPrime y)]
    simpa only [dist_eq_norm, Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr h), NNReal.coe_ofNat] using hb h

/-- On every interval the specified second derivative integrates to the change of
the first derivative, so no point masses occur at either gluing point. -/
theorem integral_cutoffQuotientSecond (a b : ℝ) :
    (∫ x in a..b, cutoffQuotientSecond x) = cutoffQuotientPrime b - cutoffQuotientPrime a := by
  calc
    _ = ∫ x in a..b, deriv cutoffQuotientPrime x := intervalIntegral.integral_congr_ae
      (ae_hasDerivAt_cutoffQuotientPrime.mono fun _ h _ ↦ h.deriv.symm)
    _ = _ := lipschitzWith_cutoffQuotientPrime.lipschitzOnWith.absolutelyContinuousOnInterval.integral_deriv_eq_sub

end RiemannMasullo.WeakCardinal
