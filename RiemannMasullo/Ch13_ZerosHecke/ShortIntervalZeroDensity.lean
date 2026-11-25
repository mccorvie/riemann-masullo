module

public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.NumberTheory.Chebyshev

/-!
# Zero-density bounds for short intervals

The difference of two truncations of the von Mangoldt explicit formula contains the terms
`(b ^ ρ - a ^ ρ) / ρ`. A sublinear bound for the number of zeros with large real part
gives a saving on a short logarithmic interval. All finite sums may include multiplicities.
This is the density step in the rational prime criterion for Theorem 12.5.1.1, pp. 519–520.
-/

@[expose] public noncomputable section

open Set MeasureTheory

namespace RiemannMasullo

private theorem integral_reciprocal_tail {T : ℝ} (hT : 0 < T) (h m : ℝ) :
    (∫ t in Ioi T, (Ioi h).indicator (fun u : ℝ ↦ m * u ^ (-2 : ℝ)) t) =
      m / max T h := by
  rw [setIntegral_indicator measurableSet_Ioi, Ioi_inter_Ioi, integral_const_mul,
    integral_Ioi_rpow_of_lt (by norm_num : (-2 : ℝ) < -1) (hT.trans_le (le_max_left T h))]
  norm_num [div_eq_mul_inv, Real.rpow_neg_one]

/-- Integrating a sublinear count against the inverse-square density controls the capped
reciprocal-height sum. The count and its constant may be restricted to a finite truncation. -/
theorem sum_div_max_height_le_of_count {ι : Type*} (S : Finset ι) (h m : ι → ℝ)
    {T d C : ℝ} (hT : 0 < T) (hd : d < 1)
    (hc : ∀ t ≥ T, (∑ i ∈ S with h i < t, m i) ≤ C * t ^ d) :
    (∑ i ∈ S, m i / max T (h i)) ≤ C * T ^ (d - 1) / (1 - d) := by
  let f (i : ι) (t : ℝ) := (Ioi (h i)).indicator (fun u : ℝ ↦ m i * u ^ (-2 : ℝ)) t
  have hi (i : ι) : IntegrableOn (f i) (Ioi T) := by
    exact ((integrableOn_Ioi_rpow_of_lt (by norm_num : (-2 : ℝ) < -1) hT).const_mul (m i)).indicator
      measurableSet_Ioi
  calc
    _ = ∫ t in Ioi T, ∑ i ∈ S, f i t := by
      rw [integral_finsetSum S (fun i _ ↦ hi i)]
      exact Finset.sum_congr rfl fun i _ ↦ (integral_reciprocal_tail hT (h i) (m i)).symm
    _ ≤ ∫ t in Ioi T, C * t ^ (d - 2) := by
      apply setIntegral_mono_on (integrable_finsetSum S (fun i _ ↦ hi i))
        ((integrableOn_Ioi_rpow_of_lt (by linarith : d - 2 < -1) hT).const_mul C) measurableSet_Ioi
      intro t ht
      have ht' : 0 < t := hT.trans ht
      have he : (∑ i ∈ S, f i t) = (∑ i ∈ S with h i < t, m i) * t ^ (-2 : ℝ) := by
        simp only [Finset.sum_mul, Finset.sum_filter, f, indicator_apply, mem_Ioi, ite_mul, zero_mul]
      rw [he, show d - 2 = d + -2 by ring, Real.rpow_add ht', ← mul_assoc]
      exact mul_le_mul_of_nonneg_right (hc t ht.le) (Real.rpow_nonneg ht'.le _)
    _ = _ := by
      rw [integral_const_mul, integral_Ioi_rpow_of_lt (by linarith : d - 2 < -1) hT,
        show d - 2 + 1 = d - 1 by ring, show 1 - d = -(d - 1) by ring, div_neg]
      ring

private theorem norm_cpow_interval_sub_le {a b : ℝ} (ha : 0 < a) (hab : a ≤ b)
    {z : ℂ} (hz : 0 ≤ z.re) :
    ‖(b : ℂ) ^ z - (a : ℂ) ^ z‖ ≤ 2 * b ^ z.re := by
  have hb := ha.trans_le hab
  calc
    _ ≤ ‖(b : ℂ) ^ z‖ + ‖(a : ℂ) ^ z‖ := norm_sub_le ..
    _ ≤ _ := by
      rw [Complex.norm_cpow_eq_rpow_re_of_pos ha, Complex.norm_cpow_eq_rpow_re_of_pos hb]
      linarith [Real.rpow_le_rpow ha.le hab hz]

private theorem norm_cpow_interval_quot_le {a b T : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (hT : 0 < T) (hlog : Real.log b - Real.log a ≤ T⁻¹) {z : ℂ} (hz : 0 ≤ z.re) :
    ‖((b : ℂ) ^ z - (a : ℂ) ^ z) / z‖ ≤ 2 * b ^ z.re / max T |z.im| := by
  have hb := ha.trans_le hab
  have hn : 0 ≤ 2 * b ^ z.re := by positivity
  have hden : 0 < max T |z.im| := hT.trans_le (le_max_left ..)
  by_cases hzero : z = 0
  · simpa [hzero] using div_nonneg hn hden.le
  have hz₀ := norm_pos_iff.mpr hzero
  rw [norm_div]
  by_cases hlarge : T ≤ ‖z‖
  · exact (div_le_div_of_nonneg_right (norm_cpow_interval_sub_le ha hab hz) hz₀.le).trans
      (div_le_div_of_nonneg_left hn hden (max_le hlarge (Complex.abs_im_le_norm _)))
  have hsmall := le_of_not_ge hlarge
  have hmax : max T |z.im| = T := max_eq_left ((Complex.abs_im_le_norm _).trans hsmall)
  let l := Real.log b - Real.log a
  have hl : 0 ≤ l := sub_nonneg.mpr (Real.log_le_log ha hab)
  have hx : ‖(-(l : ℂ)) * z‖ ≤ 1 := by
    rw [norm_mul, norm_neg, Complex.norm_real, Real.norm_of_nonneg hl]
    exact (mul_le_mul hlog hsmall hz₀.le (inv_nonneg.mpr hT.le)).trans_eq (inv_mul_cancel₀ hT.ne')
  have he : (a : ℂ) ^ z = (b : ℂ) ^ z * Complex.exp (-(l : ℂ) * z) := by
    rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr ha.ne'),
      Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hb.ne'), ← Complex.exp_add,
      ← Complex.ofReal_log ha.le, ← Complex.ofReal_log hb.le]
    congr 1
    simp only [l, Complex.ofReal_sub]
    ring
  rw [he, ← mul_one_sub, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hb,
    norm_sub_rev (1 : ℂ), hmax, div_le_div_iff₀ hz₀ hT]
  have hx' := Complex.norm_exp_sub_one_le hx
  rw [norm_mul, norm_neg, Complex.norm_real, Real.norm_of_nonneg hl] at hx'
  have hlT : l * T ≤ 1 := (le_div_iff₀ hT).mp (by simpa only [one_div] using hlog)
  calc
    _ ≤ b ^ z.re * (2 * (l * ‖z‖)) * T :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hx' (Real.rpow_nonneg hb.le _)) hT.le
    _ = (2 * b ^ z.re * ‖z‖) * (l * T) := by ring
    _ ≤ _ := mul_le_of_le_one_right (by positivity) hlT

/-- The contribution of the zeros in a fixed right-hand strip to the difference of two
truncated explicit formulas. A height count with exponent `d < 1` saves `T ^ (d - 1)`
when the endpoints differ by at most `1/T` in log coordinates. -/
theorem norm_shortInterval_zeroSum_le_of_density {ι : Type*} (S : Finset ι)
    (ρ : ι → ℂ) (m : ι → ℝ) {a b T d C θ : ℝ} (ha : 0 < a) (hab : a ≤ b) (hb : 1 ≤ b)
    (hT : 0 < T) (hlog : Real.log b - Real.log a ≤ T⁻¹) (hd : d < 1)
    (hm : ∀ i ∈ S, 0 ≤ m i) (hz : ∀ i ∈ S, (ρ i).re ∈ Icc 0 θ)
    (hc : ∀ t ≥ T, (∑ i ∈ S with |(ρ i).im| < t, m i) ≤ C * t ^ d) :
    ‖∑ i ∈ S, (m i : ℂ) * (((b : ℂ) ^ ρ i - (a : ℂ) ^ ρ i) / ρ i)‖ ≤
      (2 * b ^ θ) * (C * T ^ (d - 1) / (1 - d)) := by
  have hfactor : 0 ≤ 2 * b ^ θ := by positivity
  calc
    _ ≤ ∑ i ∈ S, (2 * b ^ θ) * (m i / max T |(ρ i).im|) := by
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro i hi
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (hm i hi)]
      have h := norm_cpow_interval_quot_le ha hab hT hlog (hz i hi).1
      have h' := Real.rpow_le_rpow_of_exponent_le hb (hz i hi).2
      calc
        _ ≤ m i * (2 * b ^ θ / max T |(ρ i).im|) :=
          mul_le_mul_of_nonneg_left (h.trans (div_le_div_of_nonneg_right (by linarith)
            (hT.le.trans (le_max_left ..)))) (hm i hi)
        _ = _ := by ring
    _ ≤ _ := by
      rw [← Finset.mul_sum]
      exact mul_le_mul_of_nonneg_left (sum_div_max_height_le_of_count S _ m hT hd hc) hfactor

private theorem norm_shortInterval_zeroSum_le_low {ι : Type*} (S : Finset ι)
    (ρ : ι → ℂ) (m : ι → ℝ) {a b v : ℝ} (ha : 0 < a) (hab : a ≤ b) (hb : 1 ≤ b)
    (hm : ∀ i ∈ S, 0 ≤ m i) (hz : ∀ i ∈ S, (ρ i).re ∈ Icc 0 v) :
    ‖∑ i ∈ S, (m i : ℂ) * (((b : ℂ) ^ ρ i - (a : ℂ) ^ ρ i) / ρ i)‖ ≤
      2 * b ^ v * ∑ i ∈ S, m i / ‖ρ i‖ := by
  rw [Finset.mul_sum]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro i hi
  rw [norm_mul, norm_div, Complex.norm_real, Real.norm_of_nonneg (hm i hi)]
  have h := norm_cpow_interval_sub_le ha hab (hz i hi).1
  have h' := Real.rpow_le_rpow_of_exponent_le hb (hz i hi).2
  calc
    _ ≤ m i * (2 * b ^ v / ‖ρ i‖) :=
      mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right (by linarith) (norm_nonneg _)) (hm i hi)
    _ = _ := by ring

/-- A common truncated explicit formula at both endpoints and a sublinear count of the
zeros to the right of `v` bound the Chebyshev error on the whole short interval. The two
endpoint errors and the low-strip reciprocal sum are retained explicitly. -/
theorem chebyshev_shortInterval_error_le_of_zeroDensity {ι : Type*} (S : Finset ι)
    (ρ : ι → ℂ) (m : ι → ℝ) {a b T d C θ v R₁ R₂ : ℝ}
    (ha : 0 < a) (hab : a ≤ b) (hb : 1 ≤ b) (hT : 0 < T)
    (hlog : Real.log b - Real.log a ≤ T⁻¹) (hd : d < 1)
    (hm : ∀ i ∈ S, 0 ≤ m i) (hz : ∀ i ∈ S, (ρ i).re ∈ Icc 0 θ)
    (hc : ∀ t ≥ T, (∑ i ∈ S with v < (ρ i).re ∧ |(ρ i).im| < t, m i) ≤ C * t ^ d)
    (h₁ : ‖(Chebyshev.psi a : ℂ) - a + ∑ i ∈ S, (m i : ℂ) * ((a : ℂ) ^ ρ i / ρ i)‖ ≤ R₁)
    (h₂ : ‖(Chebyshev.psi b : ℂ) - b + ∑ i ∈ S, (m i : ℂ) * ((b : ℂ) ^ ρ i / ρ i)‖ ≤ R₂) :
    |Chebyshev.psi b - Chebyshev.psi a - (b - a)| ≤ R₂ + R₁ +
      2 * b ^ θ * (C * T ^ (d - 1) / (1 - d)) +
      2 * b ^ v * (∑ i ∈ S with (ρ i).re ≤ v, m i / ‖ρ i‖) := by
  let A (x : ℝ) := ∑ i ∈ S, (m i : ℂ) * ((x : ℂ) ^ ρ i / ρ i)
  let f (i : ι) := (m i : ℂ) * (((b : ℂ) ^ ρ i - (a : ℂ) ^ ρ i) / ρ i)
  have hsum : A b - A a = ∑ i ∈ S, f i := by
    dsimp [A, f]
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i _ ↦ by ring
  let high := S.filter (fun i ↦ v < (ρ i).re)
  let low := S.filter (fun i ↦ (ρ i).re ≤ v)
  have hpart : (∑ i ∈ high, f i) + (∑ i ∈ low, f i) = A b - A a := by
    rw [hsum]
    simpa only [high, low, not_lt] using S.sum_filter_add_sum_filter_not (fun i ↦ v < (ρ i).re) f
  have hhigh : ‖∑ i ∈ high, f i‖ ≤ 2 * b ^ θ * (C * T ^ (d - 1) / (1 - d)) :=
    norm_shortInterval_zeroSum_le_of_density high ρ m ha hab hb hT hlog hd
      (fun i hi ↦ hm i (Finset.mem_filter.mp hi).1) (fun i hi ↦ hz i (Finset.mem_filter.mp hi).1)
      (fun t ht ↦ by simpa only [high, Finset.filter_filter] using hc t ht)
  have hlow : ‖∑ i ∈ low, f i‖ ≤ 2 * b ^ v * (∑ i ∈ low, m i / ‖ρ i‖) :=
    norm_shortInterval_zeroSum_le_low low ρ m ha hab hb
      (fun i hi ↦ hm i (Finset.mem_filter.mp hi).1)
      (fun i hi ↦ ⟨(hz i (Finset.mem_filter.mp hi).1).1, (Finset.mem_filter.mp hi).2⟩)
  have hdiff : ‖A b - A a‖ ≤ _ := (hpart ▸ norm_add_le _ _).trans (add_le_add hhigh hlow)
  have herr := (norm_sub_le ((Chebyshev.psi b : ℂ) - b + A b)
      ((Chebyshev.psi a : ℂ) - a + A a)).trans (add_le_add h₂ h₁)
  calc
    _ = ‖((Chebyshev.psi b : ℂ) - b + A b - ((Chebyshev.psi a : ℂ) - a + A a)) -
        (A b - A a)‖ := by
      rw [show ((Chebyshev.psi b : ℂ) - b + A b - ((Chebyshev.psi a : ℂ) - a + A a)) -
        (A b - A a) = ((Chebyshev.psi b - Chebyshev.psi a - (b - a) : ℝ) : ℂ) by push_cast; ring]
      exact (Complex.norm_real _).symm
    _ ≤ _ := by
      simpa only [add_assoc] using (norm_sub_le _ _).trans (add_le_add herr hdiff)

end RiemannMasullo
