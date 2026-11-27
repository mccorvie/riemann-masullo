module

public import RiemannMasullo.ForMathlib.NumberTheory.LSeries.Selberg.Definitions
import RiemannMasullo.ForMathlib.NumberTheory.LSeries.Selberg.Fourier.KernelSymmetry
import RiemannMasullo.ForMathlib.NumberTheory.LSeries.Selberg.Gaussian.ThetaError

public section

namespace RiemannMasullo.Selberg

private theorem norm_psi_exp_le (z : ℂ) (hc : 0 < Real.cos (2 * z.im)) :
    ‖psi (Complex.exp z)‖ ≤ Real.exp (-z.re) * (Real.sqrt (Real.cos (2 * z.im)))⁻¹ / 2 := by
  let v := Real.sqrt Real.pi * Real.exp z.re * Real.sqrt (Real.cos (2 * z.im))
  have hv : 0 < v := by dsimp [v]; positivity
  have hsum : Summable fun n : ℕ ↦ Real.exp (-(((n + 1 : ℕ) : ℝ) * v)^2) := by
    have h := Real.summable_exp_nat_mul_of_ge (neg_lt_zero.mpr (sq_pos_of_pos hv))
      (f := fun n : ℕ ↦ ((n + 1 : ℕ) : ℝ)^2) (by
        intro n
        push_cast
        nlinarith [sq_nonneg (n : ℝ), Nat.cast_nonneg (α := ℝ) n])
    simpa only [mul_pow, neg_mul, mul_comm (v ^ 2)] using h
  calc
    ‖psi (Complex.exp z)‖ ≤ theta v := by
      apply tsum_of_norm_bounded hsum.hasSum
      intro n
      apply le_of_eq
      rw [Complex.norm_exp, ← Complex.ofReal_natCast, ← Complex.ofReal_pow,
        ← Complex.ofReal_neg, ← Complex.ofReal_mul, Complex.re_ofReal_mul,
        pow_two (Complex.exp z), ← Complex.exp_add, Complex.exp_re,
        Complex.add_re, Complex.add_im, Real.exp_add, ← two_mul z.im]
      congr 1
      simp only [v, mul_pow, Real.sq_sqrt Real.pi_pos.le, Real.sq_sqrt hc.le]
      ring
    _ ≤ gaussC / v := sub_nonneg.mp (theta_error v hv).1
    _ = _ := by
      rw [gaussC, Real.exp_neg]
      dsimp [v]
      field_simp [ne_of_gt (Real.sqrt_pos.mpr Real.pi_pos)]

private theorem kernel_bound_of_cos_pos (z : ℂ) (hc : 0 < Real.cos (2 * z.im)) :
    ‖K z‖ ≤ 1/2 * (1 + (Real.sqrt (Real.cos (2 * z.im)))⁻¹) * Real.exp (-z.re/2) := by
  have hfactor : Real.exp (z.re / 2) * Real.exp (-z.re) = Real.exp (-z.re / 2) := by
    rw [← Real.exp_add]
    congr 1
    ring
  calc
    ‖K z‖ ≤ ‖Complex.exp (z/2) * psi (Complex.exp z)‖ + ‖Complex.exp (-z/2)/2‖ :=
      norm_sub_le _ _
    _ = Real.exp (z.re/2) * ‖psi (Complex.exp z)‖ + Real.exp (-z.re/2)/2 := by
      simp only [norm_mul, norm_div, Complex.norm_exp, Complex.norm_ofNat, Complex.div_ofNat_re,
        Complex.neg_re]
    _ ≤ Real.exp (z.re/2) * (Real.exp (-z.re) * (Real.sqrt (Real.cos (2 * z.im)))⁻¹ / 2)
        + Real.exp (-z.re/2)/2 := by
      gcongr
      exact norm_psi_exp_le z hc
    _ = _ := by
      linear_combination (Real.sqrt (Real.cos (2 * z.im)))⁻¹ / 2 * hfactor

/-- Card 16. On the strip |Im z| < π/4, the kernel decays as exp(−|Re z|/2) with a uniform factor
bounded by a constant times 1 + 1/√cos(2 Im z).
Titchmarsh, §10.10, p. 269, domination for rotation and inversion. -/
theorem kernel_bound : ∃ C > (0 : ℝ), ∀ z : ℂ, |z.im| < Real.pi/4 →
    ‖K z‖ ≤ C * (1 + (Real.sqrt (Real.cos (2*z.im)))⁻¹) * Real.exp (-|z.re|/2) := by
  refine ⟨1/2, by norm_num, fun z hz ↦ ?_⟩
  have hc : 0 < Real.cos (2 * z.im) := by
    apply Real.cos_pos_of_mem_Ioo
    obtain ⟨hl, hu⟩ := abs_lt.mp hz
    constructor <;> linarith
  rcases le_or_gt 0 z.re with h | h
  · simpa only [abs_of_nonneg h] using kernel_bound_of_cos_pos z hc
  · have hc' : 0 < Real.cos (2 * (-z).im) := by simpa using hc
    simpa [abs_of_neg h, (kernel_symmetry hz).1] using kernel_bound_of_cos_pos (-z) hc'

end RiemannMasullo.Selberg
