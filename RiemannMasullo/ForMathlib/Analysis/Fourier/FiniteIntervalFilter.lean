module

public import Mathlib.Analysis.Complex.Trigonometric
public import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! # High frequencies of a finite convolution of intervals

The transform of a uniform law of radius `a` is `sinh (a * z) / (a * z)`
away from the origin. Taking `N` intervals of radius `R / N` keeps the
support radius equal to `R`.
-/

public section

namespace RiemannMasullo

private theorem norm_sinh_le_exp_abs_re (z : ℂ) : ‖Complex.sinh z‖ ≤ Real.exp |z.re| := by
  rw [Complex.sinh, norm_div]
  have h := norm_sub_le (Complex.exp z) (Complex.exp (-z))
  rw [Complex.norm_exp, Complex.norm_exp, Complex.neg_re] at h
  norm_num
  linarith [Real.exp_le_exp.mpr (le_abs_self z.re), Real.exp_le_exp.mpr (neg_le_abs z.re)]

/-- On every vertical strip, the transform of `N` uniform intervals of radius
`R / N` is bounded by `exp (B * R) / R ^ N` beyond height `N`.
For `B = 1/2` and `R = 8` the bound is `exp 4 / 8 ^ N`. -/
theorem norm_sinh_div_pow_le_of_im_ge {N : ℕ} (hN : 0 < N) {R B : ℝ} (hR : 0 < R)
    {z : ℂ} (hre : |z.re| ≤ B) (him : (N : ℝ) ≤ |z.im|) :
    let w : ℂ := ((R / (N : ℝ) : ℝ) : ℂ) * z
    ‖(Complex.sinh w / w) ^ N‖ ≤ Real.exp (B * R) / R ^ N := by
  let a : ℝ := R / N
  let w : ℂ := (a : ℂ) * z
  have hn : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have ha : 0 < a := div_pos hR hn
  have haN : a * N = R := div_mul_cancel₀ R hn.ne'
  have hwr : |w.re| ≤ a * B := by
    simpa [w, Complex.mul_re, abs_mul, abs_of_pos ha] using
      mul_le_mul_of_nonneg_left hre ha.le
  have hwi : R ≤ |w.im| := by
    have ht := mul_le_mul_of_nonneg_left him ha.le
    simpa [w, Complex.mul_im, abs_mul, abs_of_pos ha, haN] using ht
  have hw : R ≤ ‖w‖ := hwi.trans (Complex.abs_im_le_norm w)
  have hfac : ‖Complex.sinh w / w‖ ≤ Real.exp (a * B) / R := by
    rw [norm_div]
    exact div_le_div₀ ((Real.exp_pos _).le)
      ((norm_sinh_le_exp_abs_re w).trans (Real.exp_le_exp.mpr hwr)) hR hw
  change ‖(Complex.sinh w / w) ^ N‖ ≤ _
  rw [norm_pow]
  calc
    _ ≤ (Real.exp (a * B) / R) ^ N := pow_le_pow_left₀ (norm_nonneg _) hfac _
    _ = Real.exp (B * R) / R ^ N := by
      rw [div_pow, ← Real.exp_nat_mul]
      congr 2
      rw [← haN]
      ring

end RiemannMasullo
