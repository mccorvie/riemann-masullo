module

public import RiemannMasullo.ForMathlib.Analysis.SpecialFunctions.Gamma.GaussDifference
public import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Logarithmic growth of digamma on closed right half-planes

Gauss's difference integral is estimated on three intervals. On the first, the
exponentials cancel to first order. On the middle interval the majorant is
`4 / t`, and the tail has exponential decay uniform on the half-plane.
-/

public noncomputable section

open Set MeasureTheory

namespace Complex

private def digammaDifferenceKernel (z : ℂ) (t : ℝ) : ℂ :=
  (exp (-(t : ℂ)) - exp (-z * t)) / (1 - exp (-(t : ℂ)))

private theorem norm_digammaDifferenceKernel {z : ℂ} {t : ℝ} (ht : 0 < t) :
    ‖digammaDifferenceKernel z t‖ =
      ‖exp (-(t : ℂ)) - exp (-z * t)‖ / (1 - Real.exp (-t)) := by
  have h : 1 - exp (-(t : ℂ)) = ((1 - Real.exp (-t) : ℝ) : ℂ) := by
    simp only [ofReal_sub, ofReal_one, ofReal_exp, ofReal_neg]
  rw [digammaDifferenceKernel, norm_div, h, norm_real, Real.norm_eq_abs,
    abs_of_nonneg (sub_nonneg.mpr (Real.exp_le_one_iff.mpr (by linarith)))]

private theorem gauss_denominator_lower {t : ℝ} (ht : 0 < t) :
    (t ≤ 1 → t / 2 ≤ 1 - Real.exp (-t)) ∧
    (1 ≤ t → 1 / 2 ≤ 1 - Real.exp (-t)) := by
  have hpos : 0 < 1 + t := by linarith
  have he : Real.exp (-t) ≤ 1 / (1 + t) := by
    rw [Real.exp_neg, ← one_div]
    exact one_div_le_one_div_of_le hpos (by linarith [Real.add_one_le_exp t])
  have hid : t / (1 + t) = 1 - 1 / (1 + t) := by
    field_simp
    ring
  have h : t / (1 + t) ≤ 1 - Real.exp (-t) := by linarith
  constructor
  · intro h1
    apply le_trans _ h
    apply (le_div_iff₀ hpos).mpr
    nlinarith [mul_nonneg ht.le (sub_nonneg.mpr h1)]
  · intro h1
    apply le_trans _ h
    apply (le_div_iff₀ hpos).mpr
    linarith

private theorem gauss_kernel_small (z : ℂ) {t : ℝ} (ht : 0 < t)
    (hy : t * (2 + ‖z‖) ≤ 1) :
    ‖digammaDifferenceKernel z t‖ ≤ 4 * (2 + ‖z‖) := by
  have hn : 0 ≤ ‖z‖ * t := mul_nonneg (norm_nonneg _) ht.le
  have h1 : t ≤ 1 := by nlinarith
  have ht' : ‖-(t : ℂ)‖ = t := by simp [Real.norm_eq_abs, abs_of_pos ht]
  have hz' : ‖-z * (t : ℂ)‖ = ‖z‖ * t := by simp [Real.norm_eq_abs, abs_of_pos ht]
  have hsmall := norm_exp_sub_one_le (x := -(t : ℂ)) (by rw [ht']; exact h1)
  have hzsmall := norm_exp_sub_one_le (x := -z * (t : ℂ)) (by rw [hz']; nlinarith)
  rw [ht'] at hsmall
  rw [hz'] at hzsmall
  have hsub := norm_sub_le (exp (-(t : ℂ)) - 1) (exp (-z * t) - 1)
  simp only [sub_sub_sub_cancel_right] at hsub
  have hd := (gauss_denominator_lower ht).1 h1
  rw [norm_digammaDifferenceKernel ht]
  apply (div_le_iff₀ (by linarith : 0 < 1 - Real.exp (-t))).mpr
  have hmul := mul_le_mul_of_nonneg_left hd (by positivity : 0 ≤ 4 * (2 + ‖z‖))
  nlinarith

private theorem gauss_numerator_le {z : ℂ} {u t : ℝ} (huz : u ≤ z.re)
    (hu1 : u ≤ 1) (ht : 0 ≤ t) :
    ‖exp (-(t : ℂ)) - exp (-z * t)‖ ≤ 2 * Real.exp (-u * t) := by
  have h1 : ‖exp (-(t : ℂ))‖ ≤ Real.exp (-u * t) := by
    rw [norm_exp, neg_re, ofReal_re]
    apply Real.exp_le_exp.mpr
    nlinarith [mul_le_mul_of_nonneg_right hu1 ht]
  have h2 : ‖exp (-z * t)‖ ≤ Real.exp (-u * t) := by
    rw [norm_exp, mul_re, neg_re, ofReal_re, ofReal_im, mul_zero, sub_zero]
    exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (neg_le_neg huz) ht)
  exact (norm_sub_le _ _).trans (by linarith)

private theorem gauss_kernel_middle {z : ℂ} {t : ℝ} (hz : 0 ≤ z.re) (ht : 0 < t)
    (ht1 : t ≤ 1) : ‖digammaDifferenceKernel z t‖ ≤ 4 * t⁻¹ := by
  have hn : ‖exp (-(t : ℂ)) - exp (-z * t)‖ ≤ 2 := by
    simpa only [neg_zero, zero_mul, Real.exp_zero, mul_one] using
      (gauss_numerator_le (u := 0) hz zero_le_one ht.le)
  have hd := (gauss_denominator_lower ht).1 ht1
  rw [norm_digammaDifferenceKernel ht, ← div_eq_mul_inv]
  apply (div_le_div_iff₀ (by linarith : 0 < 1 - Real.exp (-t)) ht).mpr
  nlinarith [mul_le_mul_of_nonneg_right hn ht.le]

private theorem gauss_kernel_tail {z : ℂ} {u t : ℝ} (huz : u ≤ z.re)
    (hu1 : u ≤ 1) (ht : 1 ≤ t) :
    ‖digammaDifferenceKernel z t‖ ≤ 4 * Real.exp (-u * t) := by
  have hpos : 0 < t := by linarith
  have hn := gauss_numerator_le huz hu1 hpos.le
  have hd := (gauss_denominator_lower hpos).2 ht
  rw [norm_digammaDifferenceKernel hpos]
  apply (div_le_iff₀ (by linarith : 0 < 1 - Real.exp (-t))).mpr
  nlinarith [mul_le_mul_of_nonneg_left hd (by positivity : 0 ≤ 4 * Real.exp (-u * t))]

private theorem integral_norm_gauss_kernel_le (z : ℂ) {u : ℝ} (hu : 0 < u)
    (huz : u ≤ z.re) (hu1 : u ≤ 1)
    (hK : IntegrableOn (digammaDifferenceKernel z) (Ioi 0)) :
    (∫ t in Ioi 0, ‖digammaDifferenceKernel z t‖) ≤
      4 + 4 * Real.log (2 + ‖z‖) + 4 / u := by
  let R := 2 + ‖z‖
  let r := 1 / R
  let f (t : ℝ) := ‖digammaDifferenceKernel z t‖
  have hR : 0 < R := by dsimp [R]; positivity
  have hr : 0 < r := one_div_pos.mpr hR
  have hr1 : r ≤ 1 := by
    apply (div_le_iff₀ hR).mpr
    dsimp [R]
    linarith [norm_nonneg z]
  have h0 : IntegrableOn f (Ioi 0) := hK.norm
  have hcut : IntegrableOn f (Ioi r) := h0.mono_set (Ioi_subset_Ioi hr.le)
  have htail : IntegrableOn f (Ioi 1) := h0.mono_set (Ioi_subset_Ioi zero_le_one)
  have hfirst : (∫ t in 0..r, f t) ≤ 4 := by
    calc
      _ ≤ ∫ _ in 0..r, 4 * R := by
        apply intervalIntegral.integral_mono_on_of_le_Ioo hr.le
        · exact (intervalIntegrable_iff_integrableOn_Ioc_of_le hr.le).mpr
            (h0.mono_set Ioc_subset_Ioi_self)
        · exact intervalIntegrable_const
        · intro t ht
          exact gauss_kernel_small z ht.1 ((le_div_iff₀ hR).mp ht.2.le)
      _ = 4 := by
        rw [intervalIntegral.integral_const, sub_zero, smul_eq_mul]
        dsimp only [r]
        field_simp
  have hmiddle : (∫ t in r..1, f t) ≤ 4 * Real.log R := by
    calc
      _ ≤ ∫ t in r..1, 4 * t⁻¹ := by
        apply intervalIntegral.integral_mono_on_of_le_Ioo hr1
        · exact (intervalIntegrable_iff_integrableOn_Ioc_of_le hr1).mpr
            (hcut.mono_set Ioc_subset_Ioi_self)
        · apply ContinuousOn.intervalIntegrable
          refine continuousOn_const.mul (continuousOn_id.inv₀ ?_)
          intro t ht
          rw [uIcc_of_le hr1] at ht
          exact (lt_of_lt_of_le hr ht.1).ne'
        · intro t ht
          exact gauss_kernel_middle (hu.le.trans huz) (hr.trans ht.1) ht.2.le
      _ = 4 * Real.log R := by
        rw [intervalIntegral.integral_const_mul, integral_inv_of_pos hr zero_lt_one]
        simp [r]
  have hlast : (∫ t in Ioi (1 : ℝ), f t) ≤ 4 / u := by
    calc
      _ ≤ ∫ t in Ioi (1 : ℝ), 4 * Real.exp (-u * t) := by
        exact setIntegral_mono_on htail ((integrableOn_exp_mul_Ioi (neg_lt_zero.mpr hu) 1).const_mul 4)
          measurableSet_Ioi (fun t ht ↦ gauss_kernel_tail huz hu1 ht.le)
      _ = 4 * (Real.exp (-u) / u) := by
        rw [MeasureTheory.integral_const_mul, integral_exp_mul_Ioi (neg_lt_zero.mpr hu), mul_one,
          neg_div_neg_eq]
      _ ≤ 4 * (1 / u) := by
        exact mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right
          (Real.exp_le_one_iff.mpr (neg_nonpos.mpr hu.le)) hu.le) (by norm_num)
      _ = 4 / u := by ring
  have hsplit0 := intervalIntegral.integral_interval_add_Ioi h0 hcut
  have hsplit1 := intervalIntegral.integral_interval_add_Ioi hcut htail
  change (∫ t in Ioi 0, f t) ≤ 4 + 4 * Real.log R + 4 / u
  linarith

/-- Quantitative logarithmic growth of the difference of digamma from its value at one.
The constant is uniform over the entire closed half-plane of real part at least `a`. -/
theorem norm_digamma_sub_one_le_log (a : ℝ) (ha : 0 < a) (z : ℂ) (hz : a ≤ z.re) :
    ‖digamma z - digamma 1‖ ≤ 4 + 4 * Real.log (2 + ‖z‖) + 4 / min a 1 := by
  obtain ⟨hi, he⟩ := gauss_logDeriv_Gamma_difference (u := 1) (v := z)
    (by norm_num) (ha.trans_le hz)
  have hK : IntegrableOn (digammaDifferenceKernel z) (Ioi 0) := by
    change IntegrableOn (fun t : ℝ ↦ (exp (-(t : ℂ)) - exp (-z * t)) /
      (1 - exp (-(t : ℂ)))) (Ioi 0)
    simpa only [neg_one_mul] using hi
  have hval : (∫ t in Ioi 0, digammaDifferenceKernel z t) = digamma z - digamma 1 := by
    simpa only [digammaDifferenceKernel, digamma_def, neg_one_mul] using he
  rw [← hval]
  exact (norm_integral_le_integral_norm _).trans
    (integral_norm_gauss_kernel_le z (lt_min ha zero_lt_one) ((min_le_left a 1).trans hz)
      (min_le_right a 1) hK)

/-- Digamma has logarithmic growth uniformly on each closed right half-plane
contained in the open half-plane of positive real part. -/
theorem exists_pos_norm_digamma_le_log (a : ℝ) (ha : 0 < a) :
    ∃ C : ℝ, 0 < C ∧ ∀ z : ℂ, a ≤ z.re →
      ‖digamma z‖ ≤ C * (1 + Real.log (2 + ‖z‖)) := by
  let C := ‖digamma 1‖ + 4 + 4 / min a 1
  have hu : 0 < min a 1 := lt_min ha zero_lt_one
  have hconst : 4 ≤ C := by
    dsimp only [C]
    linarith [norm_nonneg (digamma 1), div_nonneg (by norm_num : (0 : ℝ) ≤ 4) hu.le]
  refine ⟨C, lt_of_lt_of_le (by norm_num : (0 : ℝ) < 4) hconst, ?_⟩
  intro z hz
  have htri : ‖digamma z‖ ≤ ‖digamma z - digamma 1‖ + ‖digamma 1‖ := by
    simpa only [sub_add_cancel] using norm_add_le (digamma z - digamma 1) (digamma 1)
  have hlog : 0 ≤ Real.log (2 + ‖z‖) := Real.log_nonneg (by linarith [norm_nonneg z])
  calc
    _ ≤ C + 4 * Real.log (2 + ‖z‖) := by
      dsimp only [C]
      linarith [norm_digamma_sub_one_le_log a ha z hz]
    _ ≤ C * (1 + Real.log (2 + ‖z‖)) := by
      nlinarith only [mul_le_mul_of_nonneg_right hconst hlog]

end Complex
