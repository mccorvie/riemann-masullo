module

public import RiemannMasullo.ForMathlib.NumberTheory.LSeries.Selberg.Definitions

public section

open MeasureTheory

namespace RiemannMasullo.Selberg

private lemma norm_osc (t : ℝ) : ‖osc t‖ = 1 :=
  Complex.norm_exp_I_mul_ofReal t

private lemma norm_mult_le_length (h y : ℝ) (hh : 0 ≤ h) : ‖mult h y‖ ≤ h := by
  simpa only [mult, sub_zero, abs_of_nonneg hh, one_mul] using
    (intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := h)
      (fun u _ ↦ (norm_osc (u * y)).le))

private lemma norm_mult_mul_abs_le_two (h y : ℝ) : ‖mult h y‖ * |y| ≤ 2 := by
  by_cases hy : y = 0
  · simp [hy]
  have hc : Complex.I * (y : ℂ) ≠ 0 := mul_ne_zero Complex.I_ne_zero (by exact_mod_cast hy)
  have hphase (u : ℝ) : osc (u * y) = Complex.exp ((Complex.I * y) * u) := by
    simp only [osc, Complex.ofReal_mul]
    congr 1
    ring
  have hmult : mult h y = (osc (h * y) - 1) / (Complex.I * y) := by
    simp_rw [mult, hphase]
    rw [integral_exp_mul_complex hc]
    simp
  rw [hmult, norm_div, norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs,
    div_mul_cancel₀ _ (abs_ne_zero.mpr hy)]
  simpa only [norm_osc, norm_one, one_add_one_eq_two] using norm_sub_le (osc (h * y)) 1

/-- Card 40. For h > 0 the squared norm of the window multiplier at y is at most 8e times the
integral of q exp(−q|y|) from zero to h.
Replacement for the two frequency ranges in Titchmarsh (10.10.1), pp. 269, 275–276. -/
theorem mult_laplace (h y : ℝ) (hh : 0 < h) :
    ‖mult h y‖^2 ≤ 8*Real.exp 1 * ∫ q in (0 : ℝ)..h, q*Real.exp (-q*|y|) := by
  -- On [0, m] the damping factor is at least exp(-1).
  let m := ‖mult h y‖ / 2
  have hm : 0 ≤ m := div_nonneg (norm_nonneg _) (by norm_num)
  have hmh : m ≤ h := (half_le_self (norm_nonneg _)).trans (norm_mult_le_length h y hh.le)
  have hmy : m * |y| ≤ 1 := by
    dsimp [m]
    linarith only [norm_mult_mul_abs_le_two h y]
  have hcont : Continuous (fun q : ℝ ↦ q * Real.exp (-q * |y|)) := by fun_prop
  have hbound : m^2 / 2 * Real.exp (-1) ≤ ∫ q in (0 : ℝ)..h, q * Real.exp (-q * |y|) := calc
    m^2 / 2 * Real.exp (-1) = ∫ q in (0 : ℝ)..m, q * Real.exp (-1) := by
      rw [intervalIntegral.integral_mul_const, integral_id]
      simp
    _ ≤ ∫ q in (0 : ℝ)..m, q * Real.exp (-q * |y|) := by
      apply intervalIntegral.integral_mono_on hm
        ((continuous_id.mul continuous_const).intervalIntegrable ..) (hcont.intervalIntegrable ..)
      intro q hq
      apply mul_le_mul_of_nonneg_left _ hq.1
      apply Real.exp_le_exp.mpr
      rw [neg_mul]
      exact neg_le_neg ((mul_le_mul_of_nonneg_right hq.2 (abs_nonneg y)).trans hmy)
    _ ≤ _ := by
      apply intervalIntegral.integral_mono_interval le_rfl hm hmh _ (hcont.intervalIntegrable ..)
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with q hq
      exact mul_nonneg hq.1.le (Real.exp_pos _).le
  calc
    ‖mult h y‖^2 = 8 * Real.exp 1 * (m^2 / 2 * Real.exp (-1)) := by
      rw [Real.exp_neg]
      dsimp [m]
      field_simp
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hbound (by positivity)

end RiemannMasullo.Selberg
