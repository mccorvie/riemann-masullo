module

public import Mathlib.MeasureTheory.Integral.IntegralEqImproper
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm

/-!
# Bounds for dilating a radial profile in squared integral norm

The path `t ↦ h (r / t ^ 2)` has constant speed in the L² norm
over the positive half-line. Integrating its derivative bounds the distance
between two dilations in terms of the difference of the inverse square roots
of their scales.

The weighted estimates apply this bound to nearby columns with different real
amplitudes, restricted to a common physical window with measure `dy / y ^ 2`.
The finite-sum bounds give the cost of replacing the scales of several signed columns
and quantify how closely a cluster agrees with the sum of its amplitudes.
These are analytic estimates used to pair columns in the rational theta
comparison for Theorem 12.5.1.1, pp. 519–520.
-/

open Set MeasureTheory

public noncomputable section

namespace RiemannMasullo.RadialDilation

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

open intervalIntegral in
private theorem endpoint_sq {a b : ℝ} (hab : a ≤ b) {f d : ℝ → E}
    (hc : ContinuousOn d (Icc a b)) (hd : ∀ t ∈ Icc a b, HasDerivAt f (d t) t) :
    ‖f b - f a‖ ^ 2 ≤ (b - a) * ∫ t in a..b, ‖d t‖ ^ 2 := by
  rcases hab.eq_or_lt with rfl | h
  · simp
  have hI : ContinuousOn d (uIcc a b) := (uIcc_of_le hab) ▸ hc
  have hi := hI.norm.intervalIntegrable (μ := volume)
  have hsq : IntervalIntegrable (fun t ↦ ‖d t‖ ^ 2) volume a b := (hI.norm.pow 2).intervalIntegrable
  have ht := integral_eq_sub_of_hasDerivAt ((uIcc_of_le hab).symm ▸ hd) hI.intervalIntegrable
  have hnorm := intervalIntegral.norm_integral_le_integral_norm (f := d) (μ := volume) hab
  rw [ht] at hnorm
  have hA := mul_self_le_mul_self (norm_nonneg _) hnorm
  let m := (∫ t in a..b, ‖d t‖) / (b - a)
  have hm : m * (b - a) = ∫ t in a..b, ‖d t‖ := div_mul_cancel₀ _ (sub_ne_zero.mpr h.ne')
  have hpoly (t : ℝ) : (‖d t‖ - m) ^ 2 = ‖d t‖ ^ 2 - (2 * m) * ‖d t‖ + m ^ 2 := by ring
  have hvar := intervalIntegral.integral_nonneg (μ := volume) hab (fun t _ ↦ sq_nonneg (‖d t‖ - m))
  simp_rw [hpoly] at hvar
  rw [intervalIntegral.integral_add (hsq.sub (hi.const_mul (2 * m))) (intervalIntegrable_const (c := m ^ 2)),
    intervalIntegral.integral_sub hsq (hi.const_mul (2 * m)), intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const, smul_eq_mul, ← hm] at hvar
  rw [← hm] at hA
  nlinarith only [hA, mul_nonneg (sub_nonneg.mpr hab) hvar]

private theorem dilation_path_deriv (h h' : ℝ → E) (hd : ∀ r, HasDerivAt h (h' r) r) {t : ℝ} (ht : 0 < t) (x : ℝ) :
    HasDerivAt (fun u : ℝ ↦ h ((u⁻¹) ^ 2 * x)) ((-2 / t) • (((t⁻¹) ^ 2 * x) • h' ((t⁻¹) ^ 2 * x))) t := by
  have hi := (hasDerivAt_inv ht.ne').pow 2
  have hc := (hd ((t⁻¹) ^ 2 * x)).scomp t (hi.mul_const x)
  convert hc using 1 <;> try rfl
  rw [smul_smul]
  congr 1
  dsimp
  field_simp

private theorem dilation_row (g : ℝ → E) {t : ℝ} (ht : 0 < t) :
    (∫ r in Ioi (0 : ℝ), ‖(-2 / t) • g ((t⁻¹) ^ 2 * r)‖ ^ 2) = 4 * ∫ r in Ioi (0 : ℝ), ‖g r‖ ^ 2 := by
  simp only [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
  rw [MeasureTheory.integral_const_mul,
    integral_comp_mul_left_Ioi (fun r ↦ ‖g r‖ ^ 2) 0 (by positivity : 0 < (t⁻¹) ^ 2)]
  simp only [mul_zero, smul_eq_mul]
  field_simp
  ring

private theorem kernel_prod (g : ℝ → E) (hg : Continuous g) (hi : IntegrableOn (fun x ↦ ‖g x‖ ^ 2) (Ioi (0 : ℝ)))
    {a b : ℝ} (ha : 0 < a) :
    Integrable (fun p : ℝ × ℝ ↦ ‖(-2 / p.1) • g ((p.1⁻¹) ^ 2 * p.2)‖ ^ 2)
      ((volume.restrict (Ioc a b)).prod (volume.restrict (Ioi (0 : ℝ)))) := by
  let K (t x : ℝ) := ‖(-2 / t) • g ((t⁻¹) ^ 2 * x)‖ ^ 2
  have hm : Measurable (Function.uncurry K) := by
    change Measurable (fun p : ℝ × ℝ ↦ ‖(-2 / p.1) • g ((p.1⁻¹) ^ 2 * p.2)‖ ^ 2)
    simp only [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
    have hscale : Measurable (fun p : ℝ × ℝ ↦ (p.1⁻¹) ^ 2 * p.2) :=
      (measurable_fst.inv.pow_const 2).mul measurable_snd
    exact ((measurable_const.div measurable_fst).pow_const 2).mul ((hg.norm.measurable.comp hscale).pow_const 2)
  apply (integrable_prod_iff hm.aestronglyMeasurable).mpr
  constructor
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    have ht₀ := ha.trans ht.1
    have := (integrableOn_Ioi_comp_mul_left_iff (fun x ↦ ‖g x‖ ^ 2) 0 (by positivity : 0 < (t⁻¹) ^ 2)).mpr
      (by simpa using hi)
    change IntegrableOn (fun x : ℝ ↦ ‖(-2 / t) • g ((t⁻¹) ^ 2 * x)‖ ^ 2) (Ioi (0 : ℝ))
    simpa only [IntegrableOn, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs] using this.const_mul ((-2 / t) ^ 2)
  · have hfin : IntegrableOn (fun _ : ℝ ↦ 4 * ∫ x in Ioi (0 : ℝ), ‖g x‖ ^ 2) (Ioc a b) :=
      continuous_const.integrableOn_Ioc
    apply hfin.congr
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    change (4 * ∫ x in Ioi (0 : ℝ), ‖g x‖ ^ 2) = ∫ x in Ioi (0 : ℝ), ‖(‖(-2 / t) • g ((t⁻¹) ^ 2 * x)‖ ^ 2 : ℝ)‖
    simp only [Real.norm_eq_abs, abs_pow, abs_norm]
    exact (dilation_row g (ha.trans ht.1)).symm

private theorem dilation_inverse_sq (h h' : ℝ → E) (hc : Continuous h') (hd : ∀ r, HasDerivAt h (h' r) r)
    (hi : IntegrableOn (fun r ↦ ‖r • h' r‖ ^ 2) (Ioi (0 : ℝ))) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    (∫ r in Ioi (0 : ℝ), ‖h ((b⁻¹) ^ 2 * r) - h ((a⁻¹) ^ 2 * r)‖ ^ 2) ≤
      4 * (b - a) ^ 2 * ∫ r in Ioi (0 : ℝ), ‖r • h' r‖ ^ 2 := by
  let g (x : ℝ) := x • h' x
  let K (t x : ℝ) := ‖(-2 / t) • g ((t⁻¹) ^ 2 * x)‖ ^ 2
  have hg : Continuous g := continuous_id.smul hc
  have hprod : Integrable (Function.uncurry K)
      ((volume.restrict (Ioc a b)).prod (volume.restrict (Ioi (0 : ℝ)))) := kernel_prod g hg hi ha
  have hbound (r : ℝ) :
      ‖h ((b⁻¹) ^ 2 * r) - h ((a⁻¹) ^ 2 * r)‖ ^ 2 ≤ (b - a) * ∫ t in Ioc a b, K t r := by
    rw [← intervalIntegral.integral_of_le hab]
    apply endpoint_sq hab (d := fun t ↦ (-2 / t) • g ((t⁻¹) ^ 2 * r))
    · apply ContinuousOn.smul
      · exact continuousOn_const.div continuousOn_id (fun t ht ↦ (ha.trans_le ht.1).ne')
      · exact hg.comp_continuousOn
          ((((continuousOn_id (s := Icc a b)).inv₀ (fun t ht ↦ (ha.trans_le ht.1).ne')).pow 2).mul continuousOn_const)
    · exact fun t ht ↦ dilation_path_deriv h h' hd (ha.trans_le ht.1) r
  calc
    _ ≤ ∫ r in Ioi (0 : ℝ), (b - a) * ∫ t in Ioc a b, K t r :=
      integral_mono_of_nonneg (ae_of_all _ (fun _ ↦ sq_nonneg _)) (hprod.integral_prod_right.const_mul _)
        (ae_of_all _ hbound)
    _ = (b - a) * ∫ t in Ioc a b, ∫ r in Ioi (0 : ℝ), K t r := by
      rw [MeasureTheory.integral_const_mul]
      exact congrArg (fun z : ℝ ↦ (b - a) * z) (integral_integral_swap (f := K) hprod).symm
    _ = (b - a) * ∫ _t in Ioc a b, (4 * ∫ x in Ioi (0 : ℝ), ‖g x‖ ^ 2) := by
      congr 1
      apply setIntegral_congr_fun measurableSet_Ioc
      exact fun t ht ↦ dilation_row g (ha.trans ht.1)
    _ = _ := by
      rw [← intervalIntegral.integral_of_le hab, intervalIntegral.integral_const, smul_eq_mul]
      dsimp only [g]
      ring

/-- The squared distance between two dilations is bounded by the energy of the radial derivative. -/
theorem dilation_norm_sq (h h' : ℝ → E) (hc : Continuous h') (hd : ∀ r, HasDerivAt h (h' r) r)
    (hi : IntegrableOn (fun r ↦ ‖r • h' r‖ ^ 2) (Ioi (0 : ℝ))) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    (∫ r in Ioi (0 : ℝ), ‖h (a * r) - h (b * r)‖ ^ 2) ≤
      4 * ((Real.sqrt a)⁻¹ - (Real.sqrt b)⁻¹) ^ 2 * ∫ r in Ioi (0 : ℝ), ‖r • h' r‖ ^ 2 := by
  have hb := ha.trans_le hab
  have hp := dilation_inverse_sq h h' hc hd hi (inv_pos.mpr (Real.sqrt_pos.mpr hb))
    (inv_anti₀ (Real.sqrt_pos.mpr ha) (Real.sqrt_le_sqrt hab))
  simpa only [inv_inv, Real.sq_sqrt ha.le, Real.sq_sqrt hb.le] using hp

private theorem scale_coeff {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    4 * ((Real.sqrt a)⁻¹ - (Real.sqrt b)⁻¹) ^ 2 ≤ (b / a - 1) ^ 2 / a := by
  have h₁ := Real.sqrt_pos.mpr ha
  have hb := ha.trans_le hab
  have h₂ := Real.sqrt_pos.mpr hb
  have hle := Real.sqrt_le_sqrt hab
  have hnum : 2 * Real.sqrt a * (Real.sqrt b - Real.sqrt a) ≤ b - a := by
    nlinarith [sq_nonneg (Real.sqrt b - Real.sqrt a), Real.sq_sqrt ha.le, Real.sq_sqrt hb.le]
  have hmul : 2 * a * (Real.sqrt b - Real.sqrt a) ≤ Real.sqrt b * (b - a) := by
    have hh := mul_le_mul_of_nonneg_left hnum h₁.le
    have hh' := mul_le_mul_of_nonneg_right hle (sub_nonneg.mpr hab)
    nlinarith [Real.sq_sqrt ha.le]
  have hn : 2 * ((Real.sqrt a)⁻¹ - (Real.sqrt b)⁻¹) ≤ (b / a - 1) / (Real.sqrt a) := by
    field_simp
    nlinarith only [hmul, Real.sq_sqrt ha.le]
  have hpos := sub_nonneg.mpr (inv_anti₀ h₁ hle)
  have hs := pow_le_pow_left₀ (mul_nonneg (by norm_num) hpos) hn 2
  rw [mul_pow, div_pow, Real.sq_sqrt ha.le] at hs
  nlinarith only [hs]

private theorem difference_majorant (c d : ℝ) (x y : E) :
    ‖c • x - d • y‖ ^ 2 ≤ 2 * ((c - d) ^ 2 * ‖x‖ ^ 2 + d ^ 2 * ‖x - y‖ ^ 2) := by
  have he : c • x - d • y = (c - d) • x + d • (x - y) := by
    rw [sub_smul, smul_sub]
    abel
  rw [he]
  apply (pow_le_pow_left₀ (norm_nonneg _) (norm_add_le _ _) 2).trans
  simp only [norm_smul, Real.norm_eq_abs]
  nlinarith only [sq_nonneg (|c - d| * ‖x‖ - |d| * ‖x - y‖), sq_abs (c - d), sq_abs d,
    show (|c - d| * ‖x‖) ^ 2 = (c - d) ^ 2 * ‖x‖ ^ 2 by rw [mul_pow, sq_abs],
    show (|d| * ‖x - y‖) ^ 2 = d ^ 2 * ‖x - y‖ ^ 2 by rw [mul_pow, sq_abs]]

private theorem integrable_sq_sub_dilates (h : ℝ → E) (hc : Continuous h)
    (hi : IntegrableOn (fun r ↦ ‖h r‖ ^ 2) (Ioi (0 : ℝ))) {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (c d : ℝ) :
    IntegrableOn (fun r ↦ ‖c • h (a * r) - d • h (b * r)‖ ^ 2) (Ioi (0 : ℝ)) := by
  have ih (l : ℝ) (hl : 0 < l) : IntegrableOn (fun r ↦ ‖h (l * r)‖ ^ 2) (Ioi (0 : ℝ)) :=
    (integrableOn_Ioi_comp_mul_left_iff (fun r ↦ ‖h r‖ ^ 2) 0 hl).mpr (by simpa using hi)
  have il := (((ih a ha).const_mul (2 * c ^ 2)).add ((ih b hb).const_mul (2 * d ^ 2)))
  apply il.mono' (by
    apply Continuous.aestronglyMeasurable
    fun_prop)
  refine ae_of_all _ (fun r ↦ ?_)
  simp only [Real.norm_eq_abs, abs_pow, abs_norm]
  apply (pow_le_pow_left₀ (norm_nonneg _) (norm_sub_le _ _) 2).trans
  simp only [norm_smul, Real.norm_eq_abs, Pi.add_apply]
  nlinarith only [sq_nonneg (|c| * ‖h (a * r)‖ - |d| * ‖h (b * r)‖),
    show (|c| * ‖h (a * r)‖) ^ 2 = c ^ 2 * ‖h (a * r)‖ ^ 2 by rw [mul_pow, sq_abs],
    show (|d| * ‖h (b * r)‖) ^ 2 = d ^ 2 * ‖h (b * r)‖ ^ 2 by rw [mul_pow, sq_abs]]

private theorem weighted (h h' : ℝ → E) (hc : Continuous h') (hd : ∀ r, HasDerivAt h (h' r) r)
    (hi : IntegrableOn (fun r ↦ ‖h r‖ ^ 2) (Ioi (0 : ℝ)))
    (hg : IntegrableOn (fun r ↦ ‖r • h' r‖ ^ 2) (Ioi (0 : ℝ)))
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (c d : ℝ) :
    (∫ r in Ioi (0 : ℝ), ‖c • h (a * r) - d • h (b * r)‖ ^ 2) ≤
      2 * ((c - d) ^ 2 / a * (∫ r in Ioi (0 : ℝ), ‖h r‖ ^ 2) +
        d ^ 2 * (b / a - 1) ^ 2 / a * (∫ r in Ioi (0 : ℝ), ‖r • h' r‖ ^ 2)) := by
  have hh : Continuous h := continuous_iff_continuousAt.mpr fun r ↦ (hd r).continuousAt
  have h₁ := (integrableOn_Ioi_comp_mul_left_iff (fun r ↦ ‖h r‖ ^ 2) 0 ha).mpr (by simpa using hi)
  have h₂ : IntegrableOn (fun r ↦ ‖h (a * r) - h (b * r)‖ ^ 2) (Ioi (0 : ℝ)) := by
    simpa using integrable_sq_sub_dilates h hh hi ha (ha.trans_le hab) 1 1
  have hm := integral_nonneg (μ := volume.restrict (Ioi (0 : ℝ))) (fun r ↦ sq_nonneg ‖r • h' r‖)
  have hlo := (dilation_norm_sq h h' hc hd hg ha hab).trans (mul_le_mul_of_nonneg_right (scale_coeff ha hab) hm)
  calc
    _ ≤ ∫ r in Ioi (0 : ℝ), 2 * ((c - d) ^ 2 * ‖h (a * r)‖ ^ 2 + d ^ 2 * ‖h (a * r) - h (b * r)‖ ^ 2) :=
      integral_mono_of_nonneg (ae_of_all _ (fun r ↦ sq_nonneg _))
        (((h₁.const_mul ((c - d) ^ 2)).add (h₂.const_mul (d ^ 2))).const_mul 2)
        (ae_of_all _ (fun r ↦ difference_majorant c d _ _))
    _ = 2 * ((c - d) ^ 2 * (a⁻¹ * (∫ r in Ioi (0 : ℝ), ‖h r‖ ^ 2)) +
        d ^ 2 * (∫ r in Ioi (0 : ℝ), ‖h (a * r) - h (b * r)‖ ^ 2)) := by
      rw [integral_const_mul, integral_add (h₁.const_mul _) (h₂.const_mul _), integral_const_mul, integral_const_mul,
        integral_comp_mul_left_Ioi (fun r ↦ ‖h r‖ ^ 2) 0 ha, mul_zero, smul_eq_mul]
    _ ≤ 2 * ((c - d) ^ 2 * (a⁻¹ * (∫ r in Ioi (0 : ℝ), ‖h r‖ ^ 2)) +
        d ^ 2 * ((b / a - 1) ^ 2 / a * (∫ r in Ioi (0 : ℝ), ‖r • h' r‖ ^ 2))) := by
      gcongr
    _ = _ := by ring

private theorem reciprocal_integral (f : ℝ → ℝ) :
    (∫ y in Ioi (0 : ℝ), f y⁻¹ / y ^ 2) = ∫ r in Ioi (0 : ℝ), f r := by
  have ht := integral_comp_rpow_Ioi f (by norm_num : (-1 : ℝ) ≠ 0)
  convert ht using 1
  apply setIntegral_congr_fun measurableSet_Ioi
  intro x hx
  dsimp only
  rw [Real.rpow_neg_one, show (-1 : ℝ) - 1 = -(2 : ℝ) by norm_num,
    Real.rpow_neg (le_of_lt hx), Real.rpow_two, abs_neg, abs_one, one_mul, smul_eq_mul, div_eq_inv_mul]

private theorem reciprocal_integrable (f : ℝ → ℝ) (hf : IntegrableOn f (Ioi (0 : ℝ))) :
    IntegrableOn (fun y : ℝ ↦ f y⁻¹ / y ^ 2) (Ioi (0 : ℝ)) := by
  have hi := (integrableOn_Ioi_comp_rpow_iff' f (by norm_num : (-1 : ℝ) ≠ 0)).mpr hf
  refine (integrableOn_congr_fun ?_ measurableSet_Ioi).mpr hi
  intro x hx
  dsimp only
  rw [Real.rpow_neg_one, show (-1 : ℝ) - 1 = -(2 : ℝ) by norm_num,
      Real.rpow_neg (le_of_lt hx), Real.rpow_two, smul_eq_mul, div_eq_inv_mul]

/-- Bound the difference of two weighted reciprocal dilations on a common positive window. -/
theorem physical_weighted (h h' : ℝ → E) (hc : Continuous h') (hd : ∀ r, HasDerivAt h (h' r) r)
    (hi : IntegrableOn (fun r ↦ ‖h r‖ ^ 2) (Ioi (0 : ℝ)))
    (hg : IntegrableOn (fun r ↦ ‖r • h' r‖ ^ 2) (Ioi (0 : ℝ)))
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (c d : ℝ) {s : Set ℝ} (hs : s ⊆ Ioi 0) :
    (∫ y in s, ‖c • h (a / y) - d • h (b / y)‖ ^ 2 / y ^ 2) ≤
      2 * ((c - d) ^ 2 / a * (∫ r in Ioi (0 : ℝ), ‖h r‖ ^ 2) +
        d ^ 2 * (b / a - 1) ^ 2 / a * (∫ r in Ioi (0 : ℝ), ‖r • h' r‖ ^ 2)) := by
  let f (r : ℝ) := ‖c • h (a * r) - d • h (b * r)‖ ^ 2
  have hh : Continuous h := continuous_iff_continuousAt.mpr fun r ↦ (hd r).continuousAt
  have hf := integrable_sq_sub_dilates h hh hi ha (ha.trans_le hab) c d
  have hi' : IntegrableOn (fun y : ℝ ↦ f y⁻¹ / y ^ 2) (Ioi (0 : ℝ)) := reciprocal_integrable f hf
  calc
    _ = ∫ y in s, f y⁻¹ / y ^ 2 := by simp only [f, div_eq_mul_inv]
    _ ≤ ∫ y in Ioi (0 : ℝ), f y⁻¹ / y ^ 2 := setIntegral_mono_set hi'
      (ae_of_all _ (fun y ↦ div_nonneg (sq_nonneg _) (sq_nonneg _))) hs.eventuallySubset
    _ = ∫ r in Ioi (0 : ℝ), f r := reciprocal_integral f
    _ ≤ _ := weighted h h' hc hd hi hg ha hab c d

private theorem physical_matched (h h' : ℝ → E) (hc : Continuous h') (hd : ∀ r, HasDerivAt h (h' r) r)
    (hi : IntegrableOn (fun r ↦ ‖h r‖ ^ 2) (Ioi (0 : ℝ)))
    (hg : IntegrableOn (fun r ↦ ‖r • h' r‖ ^ 2) (Ioi (0 : ℝ)))
    {B C j : ℝ} (hB : 0 < B) (hBC : B ≤ C) (hj : 0 < j)
    {c d L A : ℝ} (hL : |c - d| ≤ L * (C / B - 1)) (hA : |d| ≤ A) {s : Set ℝ} (hs : s ⊆ Ioi 0) :
    (∫ y in s, ‖c • h (B * j / y) - d • h (C * j / y)‖ ^ 2 / y ^ 2) ≤
      2 * (C / B - 1) ^ 2 / (B * j) * (L ^ 2 * (∫ r in Ioi (0 : ℝ), ‖h r‖ ^ 2) +
        A ^ 2 * (∫ r in Ioi (0 : ℝ), ‖r • h' r‖ ^ 2)) := by
  have hw := physical_weighted h h' hc hd hi hg (mul_pos hB hj) (mul_le_mul_of_nonneg_right hBC hj.le) c d hs
  rw [mul_div_mul_right _ _ hj.ne'] at hw
  have hL' := pow_le_pow_left₀ (abs_nonneg _) hL 2
  rw [sq_abs, mul_pow] at hL'
  have hA' := pow_le_pow_left₀ (abs_nonneg _) hA 2
  rw [sq_abs] at hA'
  apply hw.trans
  calc
    _ ≤ 2 * ((L ^ 2 * (C / B - 1) ^ 2) / (B * j) * (∫ r in Ioi (0 : ℝ), ‖h r‖ ^ 2) +
        A ^ 2 * (C / B - 1) ^ 2 / (B * j) * (∫ r in Ioi (0 : ℝ), ‖r • h' r‖ ^ 2)) := by
      gcongr
    _ = _ := by ring

/-- Two columns with a common cofactor and controlled amplitude difference have weighted integral
norm bounded by the relative scale separation divided by the square root of the smaller scale. -/
theorem physical_matched_norm (h h' : ℝ → E) (hc : Continuous h') (hd : ∀ r, HasDerivAt h (h' r) r)
    (hi : IntegrableOn (fun r ↦ ‖h r‖ ^ 2) (Ioi (0 : ℝ)))
    (hg : IntegrableOn (fun r ↦ ‖r • h' r‖ ^ 2) (Ioi (0 : ℝ)))
    {B C j : ℝ} (hB : 0 < B) (hBC : B ≤ C) (hj : 0 < j)
    {c d L A : ℝ} (hL : |c - d| ≤ L * (C / B - 1)) (hA : |d| ≤ A) {s : Set ℝ} (hs : s ⊆ Ioi 0) :
    Real.sqrt (∫ y in s, ‖c • h (B * j / y) - d • h (C * j / y)‖ ^ 2 / y ^ 2) ≤
      (C / B - 1) / Real.sqrt (B * j) * Real.sqrt (2 * (L ^ 2 * (∫ r in Ioi (0 : ℝ), ‖h r‖ ^ 2) +
        A ^ 2 * (∫ r in Ioi (0 : ℝ), ‖r • h' r‖ ^ 2))) := by
  apply (Real.sqrt_le_sqrt (physical_matched h h' hc hd hi hg hB hBC hj hL hA hs)).trans_eq
  have hr := sub_nonneg.mpr ((one_le_div hB).mpr hBC)
  rw [show ∀ z : ℝ, 2 * (C / B - 1) ^ 2 / (B * j) * z = ((C / B - 1) ^ 2 / (B * j)) * (2 * z) by intro z; ring,
    Real.sqrt_mul (by positivity), Real.sqrt_div (sq_nonneg _), Real.sqrt_sq hr]

private theorem lpNorm_two_eq {α : Type*} [MeasurableSpace α] {μ : Measure α} {f : α → E}
    (hf : MemLp f 2 μ) : lpNorm f 2 μ = Real.sqrt (∫ r, ‖f r‖ ^ 2 ∂μ) := by
  rw [lpNorm_eq_integral_norm_rpow_toReal (by norm_num) (by norm_num) hf.aestronglyMeasurable]
  simp only [ENNReal.toReal_ofNat, Real.rpow_two, ← one_div, ← Real.sqrt_eq_rpow]

private theorem memLp_dilate (h : ℝ → E) (hh : Continuous h)
    (hi : IntegrableOn (fun r ↦ ‖h r‖ ^ 2) (Ioi (0 : ℝ))) {a : ℝ} (ha : 0 < a) :
    MemLp (fun r ↦ h (a * r)) 2 (volume.restrict (Ioi (0 : ℝ))) := by
  apply (memLp_two_iff_integrable_sq_norm (hh.comp (continuous_const.mul continuous_id)).aestronglyMeasurable).mpr
  exact (integrableOn_Ioi_comp_mul_left_iff (fun r ↦ ‖h r‖ ^ 2) 0 ha).mpr (by simpa using hi)

private theorem lpNorm_pair (h h' : ℝ → E) (hc : Continuous h') (hd : ∀ r, HasDerivAt h (h' r) r)
    (hi : IntegrableOn (fun r ↦ ‖h r‖ ^ 2) (Ioi (0 : ℝ)))
    (hg : IntegrableOn (fun r ↦ ‖r • h' r‖ ^ 2) (Ioi (0 : ℝ)))
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    lpNorm ((fun r ↦ h (b * r)) - fun r ↦ h (a * r)) 2 (volume.restrict (Ioi (0 : ℝ))) ≤
      (b / a - 1) / Real.sqrt a * Real.sqrt (∫ r in Ioi (0 : ℝ), ‖r • h' r‖ ^ 2) := by
  have hh : Continuous h := continuous_iff_continuousAt.mpr fun r ↦ (hd r).continuousAt
  rw [lpNorm_sub_comm, lpNorm_two_eq ((memLp_dilate h hh hi ha).sub (memLp_dilate h hh hi (ha.trans_le hab)))]
  have hm := integral_nonneg (μ := volume.restrict (Ioi (0 : ℝ))) (fun r ↦ sq_nonneg ‖r • h' r‖)
  apply (Real.sqrt_le_sqrt ((dilation_norm_sq h h' hc hd hg ha hab).trans
    (mul_le_mul_of_nonneg_right (scale_coeff ha hab) hm))).trans_eq
  rw [Real.sqrt_mul (by positivity), Real.sqrt_div (sq_nonneg _),
    Real.sqrt_sq (sub_nonneg.mpr ((one_le_div ha).mpr hab))]

/-- Replacing each scale in a signed finite sum costs at most the weighted sum of its individual scale changes. -/
theorem physical_sum_sub_dilates {ι : Type*} (s : Finset ι) (a b c : ι → ℝ)
    (ha : ∀ i ∈ s, 0 < a i) (hab : ∀ i ∈ s, a i ≤ b i)
    (h h' : ℝ → E) (hc : Continuous h') (hd : ∀ r, HasDerivAt h (h' r) r)
    (hi : IntegrableOn (fun r ↦ ‖h r‖ ^ 2) (Ioi (0 : ℝ)))
    (hg : IntegrableOn (fun r ↦ ‖r • h' r‖ ^ 2) (Ioi (0 : ℝ))) :
    Real.sqrt (∫ y in Ioi (0 : ℝ),
        ‖∑ i ∈ s, c i • (h (b i / y) - h (a i / y))‖ ^ 2 / y ^ 2) ≤
      (∑ i ∈ s, |c i| * ((b i / a i - 1) / Real.sqrt (a i))) * Real.sqrt (∫ r in Ioi (0 : ℝ), ‖r • h' r‖ ^ 2) := by
  let μ := volume.restrict (Ioi (0 : ℝ))
  let f (t r : ℝ) := h (t * r)
  let v (i : ι) := c i • (f (b i) - f (a i))
  have hh : Continuous h := continuous_iff_continuousAt.mpr fun r ↦ (hd r).continuousAt
  have hv (i : ι) (hs : i ∈ s) : MemLp (v i) 2 μ :=
    ((memLp_dilate h hh hi ((ha i hs).trans_le (hab i hs))).sub (memLp_dilate h hh hi (ha i hs))).const_smul (c i)
  have he := reciprocal_integral (fun r ↦ ‖(∑ i ∈ s, v i) r‖ ^ 2)
  simp only [Finset.sum_apply, v, f, Pi.smul_apply, Pi.sub_apply, ← div_eq_mul_inv] at he
  rw [he]
  change Real.sqrt (∫ r, ‖∑ i ∈ s, v i r‖ ^ 2 ∂μ) ≤ _
  rw [← lpNorm_two_eq (memLp_finsetSum s hv)]
  have heq : (fun r ↦ ∑ i ∈ s, v i r) = ∑ i ∈ s, v i := by ext r; simp
  rw [heq, Finset.sum_mul]
  apply (lpNorm_sum_le hv (by norm_num)).trans
  refine Finset.sum_le_sum fun i hs ↦ ?_
  change lpNorm (c i • (f (b i) - f (a i))) 2 μ ≤ _
  rw [lpNorm_const_smul, coe_nnNorm, Real.norm_eq_abs, mul_assoc]
  exact mul_le_mul_of_nonneg_left (lpNorm_pair h h' hc hd hi hg (ha i hs) (hab i hs)) (abs_nonneg _)

/-- A cluster of signed amplitudes in a relative scale interval of width `δ` has normalized norm
within `δ` times the total absolute amplitude times the derivative energy norm of its common profile. -/
theorem physical_cluster_norm {ι : Type*} (s : Finset ι) (b c : ι → ℝ) {a δ : ℝ} (ha : 0 < a)
    (hab : ∀ i ∈ s, a ≤ b i) (hδ : ∀ i ∈ s, b i / a - 1 ≤ δ)
    (h h' : ℝ → E) (hc : Continuous h') (hd : ∀ r, HasDerivAt h (h' r) r)
    (hi : IntegrableOn (fun r ↦ ‖h r‖ ^ 2) (Ioi (0 : ℝ)))
    (hg : IntegrableOn (fun r ↦ ‖r • h' r‖ ^ 2) (Ioi (0 : ℝ))) :
    |Real.sqrt a * Real.sqrt (∫ y in Ioi (0 : ℝ), ‖∑ i ∈ s, c i • h (b i / y)‖ ^ 2 / y ^ 2) -
      |∑ i ∈ s, c i| * Real.sqrt (∫ r in Ioi (0 : ℝ), ‖h r‖ ^ 2)| ≤
      δ * (∑ i ∈ s, |c i|) * Real.sqrt (∫ r in Ioi (0 : ℝ), ‖r • h' r‖ ^ 2) := by
  let μ := volume.restrict (Ioi (0 : ℝ))
  let v (t r : ℝ) := h (t * r)
  let F : ℝ → E := ∑ i ∈ s, c i • v (b i)
  let G : ℝ → E := (∑ i ∈ s, c i) • v a
  have hh : Continuous h := continuous_iff_continuousAt.mpr fun r ↦ (hd r).continuousAt
  have hF : MemLp F 2 μ := memLp_finsetSum' s fun i hs ↦
    (memLp_dilate h hh hi (ha.trans_le (hab i hs))).const_smul (c i)
  have hG : MemLp G 2 μ := (memLp_dilate h hh hi ha).const_smul _
  have hrev : |lpNorm F 2 μ - lpNorm G 2 μ| ≤ lpNorm (F - G) 2 μ := by
    apply abs_le.mpr
    constructor
    · linarith only [lpNorm_le_lpNorm_add_lpNorm_sub (f := G) hF (by norm_num : (1 : ENNReal) ≤ 2)]
    · linarith only [lpNorm_le_lpNorm_add_lpNorm_sub' (f := F) hG (by norm_num : (1 : ENNReal) ≤ 2)]
  have hFd := reciprocal_integral (fun r ↦ ‖F r‖ ^ 2)
  simp only [F, v, Finset.sum_apply, Pi.smul_apply, ← div_eq_mul_inv] at hFd
  have hGn : lpNorm G 2 μ = |∑ i ∈ s, c i| * (Real.sqrt (∫ r in Ioi (0 : ℝ), ‖h r‖ ^ 2) / Real.sqrt a) := by
    change lpNorm ((∑ i ∈ s, c i) • v a) 2 μ = _
    rw [lpNorm_const_smul, coe_nnNorm, Real.norm_eq_abs, lpNorm_two_eq (memLp_dilate h hh hi ha)]
    rw [integral_comp_mul_left_Ioi (fun r ↦ ‖h r‖ ^ 2) 0 ha, mul_zero, smul_eq_mul,
      Real.sqrt_mul (inv_nonneg.mpr ha.le), Real.sqrt_inv, div_eq_inv_mul]
  have he : ∀ r, F r - G r = ∑ i ∈ s, c i • (h (b i * r) - h (a * r)) := by
    intro r
    simp [F, G, v, Finset.sum_smul, smul_sub, Finset.sum_sub_distrib]
  have hdif := reciprocal_integral (fun r ↦ ‖(F - G) r‖ ^ 2)
  simp only [Pi.sub_apply, he, ← div_eq_mul_inv] at hdif
  have hs := physical_sum_sub_dilates s (fun _ ↦ a) b c (fun _ _ ↦ ha) hab h h' hc hd hi hg
  rw [hdif] at hs
  have hdif' : lpNorm (F - G) 2 μ ≤ (∑ i ∈ s, |c i| * ((b i / a - 1) / Real.sqrt a)) *
      Real.sqrt (∫ r in Ioi (0 : ℝ), ‖r • h' r‖ ^ 2) := by
    rw [lpNorm_two_eq (hF.sub hG)]
    simpa only [Pi.sub_apply, he] using hs
  have hC : (∑ i ∈ s, |c i| * ((b i / a - 1) / Real.sqrt a)) ≤
      (∑ i ∈ s, |c i|) * (δ / Real.sqrt a) := by
    rw [Finset.sum_mul]
    exact Finset.sum_le_sum fun i hi ↦ mul_le_mul_of_nonneg_left
      (div_le_div_of_nonneg_right (hδ i hi) (Real.sqrt_nonneg _)) (abs_nonneg _)
  have hbound := (hrev.trans hdif').trans (mul_le_mul_of_nonneg_right hC (Real.sqrt_nonneg _))
  have hscale := mul_le_mul_of_nonneg_left hbound (Real.sqrt_nonneg a)
  rw [← abs_of_nonneg (Real.sqrt_nonneg a), ← abs_mul, mul_sub, hGn] at hscale
  have hFn : Real.sqrt (∫ y in Ioi (0 : ℝ), ‖∑ i ∈ s, c i • h (b i / y)‖ ^ 2 / y ^ 2) =
      lpNorm F 2 μ := by
    rw [hFd, lpNorm_two_eq hF]
    simp only [F, v, μ, Finset.sum_apply, Pi.smul_apply]
  rw [hFn]
  simp only [abs_of_nonneg (Real.sqrt_nonneg a)] at hscale
  have cancellation (p q : ℝ) : Real.sqrt a * (p * (q / Real.sqrt a)) = p * q := by
    field_simp [(Real.sqrt_pos.mpr ha).ne']
  rw [cancellation, ← mul_assoc (Real.sqrt a), cancellation, mul_comm _ δ] at hscale
  exact hscale

end RiemannMasullo.RadialDilation
