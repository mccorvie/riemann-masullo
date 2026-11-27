module

public import Mathlib.NumberTheory.LSeries.RiemannZeta
public import Mathlib.Analysis.Meromorphic.Order
import Mathlib.NumberTheory.Harmonic.ZetaAsymp
import Mathlib.Analysis.Meromorphic.NormalForm
import RiemannMasullo.External.HardyCriticalLine.ZetaFirstApproximation

/-!
# Low-height nonvanishing and a residue test for the Riemann zeta function

Centered Euler summation excludes rational zeta zeros in the right half of the critical strip
up to absolute height one half. Every vertical progression of step one half meets this region.
If the multiplicities satisfy the two-neighbor mean-value equation on such a line, they
vanish on the entire line. This is the residue equation for the multiplier
`1 - cos(x/2)` in the first-prime form of the comparison in Theorem 12.5.1.1, pp. 519–520.
-/

@[expose] public noncomputable section

open Complex Filter MeasureTheory Set Topology HardyCriticalLine
open scoped ComplexConjugate

namespace RiemannMasullo

private theorem zetaSmallBox_integral_le (z : ℂ) (hσ : 0 < z.re) :
    ‖∫ u in Ioi (1 : ℝ), zetaFirstApproximationRealSawtooth u * (u : ℂ) ^ (-(z + 1))‖ ≤
      1 / (2 * z.re) := by
  have hp : -(z.re + 1) < -1 := by linarith
  have hm := (integrableOn_Ioi_rpow_of_lt hp (zero_lt_one : (0 : ℝ) < 1)).const_mul (1/2 : ℝ)
  refine (norm_integral_le_of_norm_le hm ?_).trans_eq ?_
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    have hu' : 0 < u := zero_lt_one.trans hu
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hu']
    simp only [Complex.neg_re, Complex.add_re, Complex.one_re]
    exact mul_le_mul_of_nonneg_right (norm_zetaFirstApproximationRealSawtooth_le_half _)
      (Real.rpow_nonneg hu'.le _)
  · rw [integral_const_mul, integral_Ioi_rpow_of_lt hp zero_lt_one, Real.one_rpow]
    ring_nf

private theorem zetaSmallBox_estimate_pos (z : ℂ) (hσ : 0 < z.re) (ht : 0 < z.im) :
    ‖(z - 1) * riemannZeta z - (z + 1) / 2‖ ≤ ‖z - 1‖ * ‖z‖ / (2 * z.re) := by
  have hz : z ≠ 1 := fun e ↦ by simp [e] at ht
  rw [riemannZeta_eq_eulerSawtooth_of_re_pos_of_im_pos hσ ht]
  have halg (J : ℂ) : (z - 1) * (1 / (z - 1) + 1 / 2 - z * J) - (z + 1) / 2 =
      -((z - 1) * z * J) := by
    field_simp [sub_ne_zero.mpr hz]
    ring
  rw [halg, norm_neg, norm_mul, norm_mul]
  simpa [div_eq_mul_inv] using mul_le_mul_of_nonneg_left (zetaSmallBox_integral_le z hσ)
    (mul_nonneg (norm_nonneg _) (norm_nonneg _))

private theorem zetaSmallBox_estimate_upper (z : ℂ) (hσ : 0 < z.re) (ht : 0 ≤ z.im) (hz : z ≠ 1) :
    ‖(z - 1) * riemannZeta z - (z + 1) / 2‖ ≤ ‖z - 1‖ * ‖z‖ / (2 * z.re) := by
  let W (t : ℝ) := z + (t : ℂ) * I
  have hw : Tendsto W (𝓝[>] (0 : ℝ)) (𝓝 z) := by
    have h : Continuous W := by unfold W; fun_prop
    simpa [W] using ((h.tendsto (0 : ℝ)).mono_left (nhdsWithin_le_nhds (s := Ioi (0 : ℝ))))
  have hζ := (differentiableAt_riemannZeta hz).continuousAt.tendsto.comp hw
  have hl := (((hw.sub_const 1).mul hζ).sub ((hw.add_const 1).div_const 2)).norm
  have hr := (((hw.sub_const 1).norm.mul hw.norm).div_const (2 * z.re))
  apply le_of_tendsto_of_tendsto hl hr
  filter_upwards [self_mem_nhdsWithin] with t ht'
  have hwre : (W t).re = z.re := by simp [W]
  have hwim : 0 < (W t).im := by simpa [W] using add_pos_of_nonneg_of_pos ht ht'
  simpa only [hwre, Function.comp_apply] using zetaSmallBox_estimate_pos (W t) (hwre ▸ hσ) hwim

private theorem riemannZeta_ne_zero_of_low_box_upper (z : ℂ) (hlo : 1/2 ≤ z.re) (hhi : z.re ≤ 1)
    (ht : 0 ≤ z.im) (ht' : z.im ≤ 1/2) (hz : z ≠ 1) : riemannZeta z ≠ 0 := by
  intro he
  have hσ : 0 < z.re := by linarith
  have h := zetaSmallBox_estimate_upper z hσ ht hz
  rw [he, mul_zero, zero_sub, norm_neg, norm_div] at h
  norm_num only [Complex.norm_ofNat] at h
  have ha : ‖z‖ ≤ 2 * z.re := by
    have hn := Complex.sq_norm_sub_sq_re z
    nlinarith [mul_nonneg (sub_nonneg.mpr (show z.im ≤ z.re by linarith))
      (add_nonneg hσ.le ht)]
  have hb : ‖z - 1‖ < 3/4 := by
    have hn := Complex.sq_norm_sub_sq_re (z - 1)
    simp only [Complex.sub_re, Complex.one_re, Complex.sub_im, Complex.one_im, sub_zero] at hn
    nlinarith [mul_nonneg (sub_nonneg.mpr hlo) (sub_nonneg.mpr hhi),
      mul_nonneg ht (sub_nonneg.mpr ht')]
  have hc := Complex.re_le_norm (z+1)
  simp only [Complex.add_re, Complex.one_re] at hc
  have hprod := mul_lt_mul_of_pos_right hb (mul_pos (by norm_num : (0 : ℝ)<2) hσ)
  have hab := mul_le_mul_of_nonneg_left ha (norm_nonneg (z-1))
  have hle := (le_div_iff₀ (by positivity : 0 < 2 * z.re)).mp h
  nlinarith [mul_le_mul_of_nonneg_right hc hσ.le,
    mul_nonneg hσ.le (sub_nonneg.mpr hlo)]

/-- Euler summation excludes all nontrivial rational zeta zeros in the right half of
the critical strip up to absolute height one half. -/
theorem riemannZeta_ne_zero_of_low_box (z : ℂ) (hlo : 1/2 ≤ z.re) (hhi : z.re ≤ 1)
    (ht : |z.im| ≤ 1/2) (hz : z ≠ 1) : riemannZeta z ≠ 0 := by
  rcases le_total 0 z.im with hp | hn
  · exact riemannZeta_ne_zero_of_low_box_upper z hlo hhi hp (le_trans (le_abs_self _) ht) hz
  · have hc : conj z ≠ 1 := fun he ↦ hz (by simpa using congrArg conj he)
    have hh : (conj z).im ≤ 1/2 := (neg_le_abs z.im).trans ht
    have h := riemannZeta_ne_zero_of_low_box_upper (conj z) hlo hhi (by simpa) hh hc
    simpa [riemannZeta_conj] using h

private theorem zetaSmallBox_propagate (m : ℝ → ℕ)
    (hrel : ∀ t, 2 * m t = m (t + 1/2) + m (t - 1/2))
    (hlow : ∀ t, |t| ≤ 1/2 → m t = 0) (t : ℝ) : m t = 0 := by
  let n : ℤ := round (2 * t)
  let u := t - (n : ℝ)/2
  have hu : m u = 0 := by
    apply hlow
    have h := abs_le.mp (abs_sub_round (2 * t))
    apply abs_le.mpr
    dsimp [u, n]
    constructor <;> linarith
  have hstep (x : ℝ) (hx : m x = 0) : m (x+1/2) = 0 ∧ m (x-1/2) = 0 := by
    have h := hrel x
    rw [hx] at h
    omega
  have hall (k : ℤ) : m (u + (k : ℝ)/2) = 0 := by
    induction k using Int.induction_on with
    | zero => simpa using hu
    | succ k ih =>
      convert (hstep _ ih).1 using 2
      push_cast
      ring
    | pred k ih =>
      convert (hstep _ ih).2 using 2
      push_cast
      ring
  simpa [u] using hall n

/-- If the true rational zero orders on a fixed vertical line satisfy the half-step residue
equation, their positive parts all vanish. The initial zero-free segment is unconditional. -/
theorem riemannZeta_order_toNat_eq_zero_of_half_step {σ : ℝ} (hσ : 1/2 ≤ σ) (hσ' : σ < 1)
    (hr : let m := fun t : ℝ ↦ (meromorphicOrderAt riemannZeta ((σ : ℂ) + (t : ℂ) * I)).untop₀.toNat
          ∀ t, 2 * m t = m (t+1/2) + m (t-1/2)) (t : ℝ) :
    (meromorphicOrderAt riemannZeta ((σ : ℂ) + (t : ℂ) * I)).untop₀.toNat = 0 := by
  refine zetaSmallBox_propagate _ hr (fun u hu ↦ ?_) t
  let z := (σ : ℂ) + (u : ℂ) * I
  have hzr : z.re = σ := by simp [z]
  have hzi : z.im = u := by simp [z]
  have hz : z ≠ 1 := fun e ↦ by
    simp [e] at hzr
    linarith
  have hne := riemannZeta_ne_zero_of_low_box z (hzr ▸ hσ) (hzr ▸ hσ'.le) (hzi ▸ hu) hz
  have horder := (analyticOn_riemannZeta z hz).meromorphicNFAt.meromorphicOrderAt_eq_zero_iff.mpr hne
  change (meromorphicOrderAt riemannZeta z).untop₀.toNat = 0
  simp [horder]

/-- The half-step residue equation for the actual rational zeta multiplicities rules
out every zero on the vertical line, at arbitrary height. -/
theorem riemannZeta_ne_zero_of_half_step {σ : ℝ} (hσ : 1/2 ≤ σ) (hσ' : σ < 1)
    (hr : let m := fun t : ℝ ↦ (meromorphicOrderAt riemannZeta ((σ : ℂ) + (t : ℂ) * I)).untop₀.toNat
          ∀ t, 2 * m t = m (t+1/2) + m (t-1/2)) (t : ℝ) :
    riemannZeta ((σ : ℂ) + (t : ℂ) * I) ≠ 0 := by
  let z := (σ : ℂ) + (t : ℂ) * I
  let U := {w : ℂ | w.re < 1}
  have ha (w : ℂ) (hw : w ∈ U) : AnalyticAt ℂ riemannZeta w := by
    apply analyticOn_riemannZeta
    rintro rfl
    exact (lt_irrefl (1 : ℝ)) hw
  have hm : MeromorphicOn riemannZeta U := fun w hw ↦ (ha w hw).meromorphicAt
  have hs : (σ : ℂ) ∈ U := hσ'
  have hz : z ∈ U := by simpa [z,U] using hσ'
  have hσne : (σ : ℂ) ≠ 1 := fun e ↦ by
    rw [e] at hs
    exact (lt_irrefl (1 : ℝ)) hs
  have h0 := (ha _ hs).meromorphicNFAt.meromorphicOrderAt_eq_zero_iff.mpr
    (riemannZeta_ne_zero_of_low_box (σ : ℂ) hσ hσ'.le (by simp) hσne)
  have hfin := hm.meromorphicOrderAt_ne_top_of_isPreconnected
    (convex_halfSpace_re_lt 1).isPreconnected hs hz (by simp [h0])
  intro hzero
  have hp : 0 < meromorphicOrderAt riemannZeta z := by
    apply (tendsto_zero_iff_meromorphicOrderAt_pos (hm z hz)).mp
    change riemannZeta z = 0 at hzero
    rw [← hzero]
    exact (ha z hz).continuousAt.continuousWithinAt
  rw [← WithTop.coe_untop₀_of_ne_top hfin] at hp
  have hint : 0 < (meromorphicOrderAt riemannZeta z).untop₀ := WithTop.coe_lt_coe.mp hp
  have hn := riemannZeta_order_toNat_eq_zero_of_half_step hσ hσ' hr t
  change (meromorphicOrderAt riemannZeta z).untop₀.toNat = 0 at hn
  omega

end RiemannMasullo
