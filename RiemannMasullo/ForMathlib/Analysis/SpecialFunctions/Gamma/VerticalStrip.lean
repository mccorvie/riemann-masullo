module

public import RiemannMasullo.ForMathlib.Analysis.SpecialFunctions.Gamma.Bounds
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.Real.Pi.Bounds

/-! # Bounds for reciprocal gamma functions on positive vertical strips -/

@[expose] public section

open Complex MeasureTheory Set
open scoped Topology ComplexConjugate

namespace RiemannMasullo

/-- Reflection bounds the reciprocal of gamma on the central line with
exponential rate π/2. -/
private theorem norm_inv_Gamma_half (w : ℂ) (hw : w.re = 1 / 2) :
    ‖(Complex.Gamma w)⁻¹‖ ≤ Real.exp (Real.pi * |w.im| / 2) := by
  have hc : 1 - w = conj w := by apply Complex.ext <;> simp [hw] ; ring
  have he := congrArg (fun t : ℂ ↦ ‖t⁻¹‖) (Complex.Gamma_mul_Gamma_one_sub w)
  simp only [hc, Complex.Gamma_conj, inv_div, norm_div, norm_inv, norm_mul, Complex.norm_conj,
    Complex.norm_of_nonneg Real.pi_pos.le, mul_inv] at he
  have hSin (z : ℂ) : ‖Complex.sin z‖ ≤ Real.exp |z.im| := by
    have h := norm_sub_le (Complex.exp (-z * Complex.I)) (Complex.exp (z * Complex.I))
    have he := congrArg (fun a : ℂ ↦ ‖a‖) (Complex.two_sin z)
    simp only [norm_mul, Complex.norm_I, mul_one] at he
    norm_num [Complex.norm_exp, Complex.mul_re] at he h
    linarith [Real.exp_le_exp.mpr (le_abs_self z.im), Real.exp_le_exp.mpr (neg_le_abs z.im)]
  have h := (div_le_self (norm_nonneg (Complex.sin (Real.pi * w)))
    (by linarith [Real.pi_gt_three] : 1 ≤ Real.pi)).trans (hSin ((Real.pi : ℂ) * w))
  rw [← he, Complex.im_ofReal_mul, abs_mul, abs_of_pos Real.pi_pos] at h
  have he₂ : Real.exp (Real.pi * |w.im|) = Real.exp (Real.pi * |w.im| / 2) ^ 2 := by
    rw [sq, ← Real.exp_add, add_halves]
  rw [he₂] at h
  rw [norm_inv]
  nlinarith [Real.exp_pos (Real.pi * |w.im| / 2)]

/-- In the positive half-plane a Beta integral compares gamma at height t
to gamma at the same height on the central line. -/
theorem exists_norm_inv_Gamma_le_half_exp_on_strip (a b : ℝ) (ha : 0 < a) :
    ∃ C > 0, ∀ z : ℂ, z.re ∈ Icc a b →
      ‖(Complex.Gamma z)⁻¹‖ ≤ C * (1 + |z.im|) * Real.exp (Real.pi * |z.im| / 2) := by
  let k (u v : ℂ) (x : ℝ) := (x : ℂ) ^ (u - 1) * (1 - (x : ℂ)) ^ (v - 1)
  let B := ∫ x : ℝ in 0..1, ‖k (1/2) (1/2) x‖
  have hs : ContinuousOn (fun t : ℝ ↦ (Real.Gamma t)⁻¹) (Icc (a + 1/2) (b + 1/2)) := by
    have hdom : Icc (a + 1/2) (b + 1/2) ⊆ Ioi (0 : ℝ) := fun x hx ↦ by
      change 0 < x; linarith [hx.1]
    exact (Real.differentiableOn_Gamma_Ioi.continuousOn.mono hdom).inv₀ fun x hx ↦
      (Real.Gamma_pos_of_pos (hdom hx)).ne'
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn hs
  let C := (1 + |b|) * (1 + |B|) * (1 + |M|)
  refine ⟨C, by dsimp [C]; positivity, fun z hz ↦ ?_⟩
  let w : ℂ := ⟨1/2, z.im⟩
  let v := z.re + 1/2
  have hw : w.re = 1/2 := rfl
  have hv : 0 < v := by dsimp [v]; linarith [hz.1]
  have hsum : w + (v : ℂ) = z + 1 := by apply Complex.ext <;> simp [w,v] ; ring
  have hβ : ‖Complex.betaIntegral w (v : ℂ)‖ ≤ B := by
    apply (intervalIntegral.norm_integral_le_integral_norm zero_le_one).trans
    apply intervalIntegral.integral_mono_on_of_le_Ioo zero_le_one
      (Complex.betaIntegral_convergent (by change (0 : ℝ) < 1/2; norm_num) hv).norm
      (Complex.betaIntegral_convergent (u := (1/2 : ℂ)) (v := (1/2 : ℂ)) (by norm_num) (by norm_num)).norm
    intro x hx
    have hy : 0 < 1 - x := sub_pos.mpr hx.2
    simp only [norm_mul, ← Complex.ofReal_one, ← Complex.ofReal_sub,
      Complex.norm_cpow_eq_rpow_re_of_pos hx.1, Complex.norm_cpow_eq_rpow_re_of_pos hy]
    apply mul_le_mul _ _ (Real.rpow_nonneg hy.le _) (Real.rpow_nonneg hx.1.le _)
    · simp [hw]
    · apply Real.rpow_le_rpow_of_exponent_ge hy (by linarith [hx.1])
      simp [v]; linarith [hz.1]
  have he := Complex.Gamma_mul_Gamma_eq_betaIntegral (s := w) (t := (v : ℂ))
    (show 0 < w.re by rw [hw]; norm_num) hv
  rw [hsum, Complex.Gamma_add_one z (show z ≠ 0 from fun h ↦ by
    have h₀ := ha.trans_le hz.1; simp [h] at h₀)] at he
  have hwG : Complex.Gamma w ≠ 0 := Complex.Gamma_ne_zero_of_re_pos (by rw [hw]; norm_num)
  have hzG : Complex.Gamma z ≠ 0 := Complex.Gamma_ne_zero_of_re_pos (ha.trans_le hz.1)
  have hvG : Complex.Gamma (v : ℂ) ≠ 0 := Complex.Gamma_ne_zero_of_re_pos hv
  have hquot : (Complex.Gamma z)⁻¹ =
      z * Complex.betaIntegral w v * (Complex.Gamma (v : ℂ))⁻¹ * (Complex.Gamma w)⁻¹ := by
    field_simp [hwG, hzG, hvG]
    linear_combination he
  have hzN : ‖z‖ ≤ (1 + |b|) * (1 + |z.im|) := by
    refine (Complex.norm_le_abs_re_add_abs_im z).trans ?_
    rw [abs_of_pos (ha.trans_le hz.1)]
    nlinarith [hz.2, le_abs_self b, abs_nonneg z.im, mul_nonneg (abs_nonneg b) (abs_nonneg z.im)]
  have hvM : ‖(Complex.Gamma (v : ℂ))⁻¹‖ ≤ 1 + |M| := by
    rw [Complex.Gamma_ofReal, ← Complex.ofReal_inv, Complex.norm_real]
    exact (hM v ⟨by dsimp [v]; linarith [hz.1], by dsimp [v]; linarith [hz.2]⟩).trans
      (by linarith [le_abs_self M])
  rw [hquot, norm_mul, norm_mul, norm_mul]
  calc
    _ ≤ ((1 + |b|) * (1 + |z.im|)) * (1 + |B|) * (1 + |M|) * Real.exp (Real.pi * |z.im| / 2) := by
      gcongr
      · exact hβ.trans (by linarith [le_abs_self B])
      · exact norm_inv_Gamma_half w hw
    _ = _ := by dsimp [C]; ring

/-- A fixed complex shift of the real archimedean factor costs a constant
on a positive strip. The exponential rate is π/4 in the original height. -/
theorem exists_norm_inv_GammaReal_add_le_on_strip (a b : ℝ) (ha : 0 < a) (w : ℂ) (hw : 0 ≤ w.re) :
    ∃ C > 0, ∀ s : ℂ, s.re ∈ Icc a b →
      ‖(Complex.Gammaℝ (s + w))⁻¹‖ ≤ C * ((1 + |s.im|) * Real.exp (Real.pi * |s.im| / 4)) := by
  let A := (a + w.re) / 2
  let B := (b + w.re) / 2
  obtain ⟨C, hC, hΓ⟩ := exists_norm_inv_Gamma_le_half_exp_on_strip A B
    (by dsimp [A]; linarith)
  let P := Real.pi ^ B
  refine ⟨C * (1 + |w.im|) * Real.exp (Real.pi * |w.im| / 4) * P, by dsimp [P]; positivity,
    fun s hs ↦ ?_⟩
  let z := (s + w) / 2
  have hz : z.re ∈ Icc A B := by
    simp only [z, A, B, Complex.div_ofNat_re, Complex.add_re]
    exact ⟨by linarith [hs.1], by linarith [hs.2]⟩
  have him : |z.im| ≤ (|s.im| + |w.im|) / 2 := by
    simp only [z, Complex.div_ofNat_im, Complex.add_im, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    exact div_le_div_of_nonneg_right (abs_add_le _ _) (by norm_num)
  have hpoly : 1 + |z.im| ≤ (1 + |w.im|) * (1 + |s.im|) := by
    nlinarith [abs_nonneg w.im, abs_nonneg s.im, mul_nonneg (abs_nonneg w.im) (abs_nonneg s.im)]
  have hexp : Real.exp (Real.pi * |z.im| / 2) ≤
      Real.exp (Real.pi * |w.im| / 4) * Real.exp (Real.pi * |s.im| / 4) := by
    rw [← Real.exp_add, Real.exp_le_exp]
    linarith [mul_le_mul_of_nonneg_left him Real.pi_pos.le]
  rw [Complex.Gammaℝ_def, mul_inv_rev, neg_div, ← Complex.cpow_neg, neg_neg,
    norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos Real.pi_pos]
  change ‖(Complex.Gamma z)⁻¹‖ * Real.pi ^ z.re ≤ _
  calc
    _ ≤ (C * ((1 + |w.im|) * (1 + |s.im|)) *
        (Real.exp (Real.pi * |w.im| / 4) * Real.exp (Real.pi * |s.im| / 4))) * P := by
      refine mul_le_mul ((hΓ z hz).trans ?_) (Real.rpow_le_rpow_of_exponent_le
        (by linarith [Real.pi_gt_three]) hz.2) (Real.rpow_nonneg Real.pi_pos.le _) (by positivity)
      gcongr
    _ = _ := by ring

end RiemannMasullo
