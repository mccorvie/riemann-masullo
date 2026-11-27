module

public import RiemannMasullo.ForMathlib.NumberTheory.LSeries.Selberg.Definitions

import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.IntervalIntegral.MeanValue

public section

namespace RiemannMasullo.Selberg

open MeasureTheory Set Filter

/-- Change variables to the square, making the phase linear. -/
private theorem pairInt_eq_linear_phase (P Q q : ℝ) :
    pairInt P Q q = ∫ v in Ioi (1 : ℝ),
      (v ^ ((-q - 1) / 2) * Real.exp (-P * v) / 2) •
        Complex.exp (Complex.I * (Q : ℂ) * v) := by
  rw [pairInt]
  conv_rhs => rw [← integral_comp_rpow_Ioi_of_pos' (p := 2) (by norm_num) zero_le_one]
  simp only [Real.one_rpow, Real.rpow_two, show (2 : ℝ) - 1 = 1 by norm_num, Real.rpow_one]
  refine setIntegral_congr_fun measurableSet_Ioi fun x hx ↦ ?_
  have hx' : 0 < x := lt_trans zero_lt_one hx
  have hpow : (x ^ 2) ^ ((-q - 1) / 2) * x = x ^ (-q) := by
    rw [← Real.rpow_natCast_mul hx'.le 2, ← Real.rpow_add_one hx'.ne']
    congr 1
    push_cast
    ring
  rw [smul_smul, show 2 * x * ((x ^ 2) ^ ((-q - 1) / 2) * Real.exp (-P * x ^ 2) / 2) =
    x ^ (-q) * Real.exp (-P * x ^ 2) by rw [← hpow]; ring]
  simp only [Complex.real_smul, Complex.ofReal_mul, Complex.ofReal_exp, Complex.ofReal_neg,
    Complex.ofReal_pow, mul_assoc, ← Complex.exp_add]
  congr 2
  ring

/-- The integral of a unit phase over any finite interval is bounded by its endpoint terms. -/
private theorem linear_phase_bound (Q a b : ℝ) (hQ : Q ≠ 0) :
    ‖∫ v in a..b, Complex.exp (Complex.I * (Q : ℂ) * v)‖ ≤ 2 / |Q| := by
  have hnorm (x : ℝ) : ‖Complex.exp (Complex.I * (Q : ℂ) * x)‖ = 1 := by
    simp [Complex.norm_exp, Complex.mul_re]
  rw [integral_exp_mul_complex (mul_ne_zero Complex.I_ne_zero (by exact_mod_cast hQ)),
    norm_div, norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs]
  gcongr
  simpa only [hnorm, one_add_one_eq_two] using
    norm_sub_le (Complex.exp (Complex.I * (Q : ℂ) * b)) (Complex.exp (Complex.I * (Q : ℂ) * a))

/-- Card 30. For positive damping P, nonzero phase coefficient Q, and q ≥ 0, the weighted Gaussian
pair integral has norm at most 2 exp(−P)/|Q|.
Titchmarsh, §10.16, p. 274, first unnumbered display. -/
theorem oscillatory_pair (P Q q : ℝ) (hP : 0 < P) (hQ : Q ≠ 0) (hq : 0 ≤ q) :
    ‖pairInt P Q q‖ ≤ 2*Real.exp (-P)/|Q| := by
  let r := (-q - 1) / 2
  let w (v : ℝ) := v ^ r * Real.exp (-P * v) / 2
  let phase (v : ℝ) := Complex.exp (Complex.I * (Q : ℂ) * v)
  have hr : r ≤ 0 := by dsimp [r]; linarith
  have hw (v : ℝ) (hv : 1 ≤ v) : 0 ≤ w v := by
    have : 0 ≤ v := zero_le_one.trans hv
    dsimp [w]
    positivity
  have hanti : AntitoneOn w (Ici 1) := by
    intro x hx y hy hxy
    have hx' : 0 < x := zero_lt_one.trans_le hx
    dsimp [w]
    apply div_le_div_of_nonneg_right _ (by norm_num)
    exact mul_le_mul (Real.rpow_le_rpow_of_nonpos hx' hxy hr)
      (Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_left hxy (neg_nonpos.mpr hP.le)))
      (Real.exp_pos _).le (Real.rpow_nonneg hx'.le _)
  have hint : IntegrableOn (fun v ↦ w v • phase v) (Ioi 1) := by
    refine (integrableOn_exp_mul_Ioi (neg_lt_zero.mpr hP) 1).mono' ?_ ?_
    · dsimp [w, phase]
      fun_prop
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv
      have hv' : 1 ≤ v := le_of_lt hv
      have hnorm : ‖phase v‖ = 1 := by simp [phase, Complex.norm_exp, Complex.mul_re]
      rw [norm_smul, hnorm, mul_one, Real.norm_eq_abs, abs_of_nonneg (hw v hv')]
      dsimp [w]
      have hpow := Real.rpow_le_one_of_one_le_of_nonpos hv' hr
      linarith [mul_le_mul_of_nonneg_right hpow (Real.exp_pos (-P * v)).le,
        Real.exp_pos (-P * v)]
  rw [pairInt_eq_linear_phase]
  apply le_of_tendsto (intervalIntegral_tendsto_integral_Ioi 1 hint tendsto_id).norm
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with b hb
  obtain ⟨c, _, hc⟩ := exists_le_const_mul_norm_intervalIntegral_of_nonneg_of_antitoneOn
    hb (hw b hb) (hanti.mono (Icc_subset_Ici_self : Icc 1 b ⊆ Ici 1))
    (g := phase) ((by fun_prop : Continuous phase).intervalIntegrable 1 b)
  calc
    _ ≤ w 1 * (2 / |Q|) :=
      hc.trans (mul_le_mul_of_nonneg_left (linear_phase_bound Q 1 c hQ) (hw 1 le_rfl))
    _ = Real.exp (-P) / |Q| := by simp only [w, Real.one_rpow, one_mul, mul_one]; ring
    _ ≤ _ := div_le_div_of_nonneg_right (by linarith [Real.exp_pos (-P)]) (abs_nonneg Q)

end RiemannMasullo.Selberg
