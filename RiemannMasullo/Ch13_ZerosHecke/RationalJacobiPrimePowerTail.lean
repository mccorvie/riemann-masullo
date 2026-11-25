module

public import RiemannMasullo.Ch13_ZerosHecke.RationalPrimitiveCellDeficits

/-! # Prime-power completion in every Jacobi cell

The contribution from integer norms other than rational primes is uniformly
bounded by the elementary square-root estimate for the difference of the
Chebyshev functions. This includes the positive-positive cell, which can
contain squares. At fourth powers the resulting cost at each sample is
`84 J^6` over the rationals.
-/

open Finset NumberField
open scoped Classical

public noncomputable section

namespace RiemannMasullo

private theorem jacobiCell_psi_sub_theta_le (T : ℕ) (hT : 1 ≤ T) :
    Chebyshev.psi T - Chebyshev.theta T ≤ 21 * Real.sqrt T := by
  have hlog : Real.log 4 + 4 ≤ 7 := by
    linarith [Real.log_le_sub_one_of_pos (show 0 < (4 : ℝ) by norm_num)]
  have hroot (k : ℝ) (hk : 2 ≤ k) :
      Chebyshev.psi ((T : ℝ)^k⁻¹) ≤ 7 * Real.sqrt T := by
    apply (Chebyshev.psi_le_const_mul_self (by positivity)).trans
    apply mul_le_mul hlog _ (by positivity) (by norm_num)
    rw [Real.sqrt_eq_rpow, one_div]
    exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hT)
      (inv_anti₀ (by norm_num : (0 : ℝ) < 2) hk)
  linarith only [Chebyshev.psi_sub_theta_le_psi_add_psi_add_psi T,
    hroot 2 (by norm_num), hroot 3 (by norm_num), hroot 5 (by norm_num)]

/-- The contribution of composite norms in a complete quadratic Riesz cell is
at most `84 [F:ℚ] T √T` for every choice of the auxiliary integers and signs.
In particular, this bound includes the squares in the positive-positive cell. -/
theorem quadraticPrimePowerCell_sub_prime_le_sqrt {F : Type*} [Field F] [NumberField F]
    (χ : PontryaginDual (IdeleClassGroup (𝓞 F) F)) {T : ℕ} (hT : 1 ≤ T)
    {x : ℝ} (hx : x ≤ T) (u v : ℕ) (e f : ℝ) :
    |quadraticPrimePowerCellRieszSum χ T x u v e f -
      quadraticPrimeCellRieszSum χ T x u v e f| ≤
        84 * (Module.finrank ℚ F : ℝ) * T * Real.sqrt T := by
  let cell (n : ℕ) := (jacobiSym u n : ℝ) = e ∧ (jacobiSym v n : ℝ) = f
  let w (n : ℕ) : ℝ := if cell n then max (x - n) 0 else 0
  let z (S : Finset ℕ) := ∑ n ∈ S, heckeLogDerivCoefficient (ideleClassNormTwist χ 0) n * (w n : ℂ)
  have hw (n : ℕ) : ‖(w n : ℂ)‖ ≤ T := by
    by_cases h : cell n
    · simp only [w, ite_eq_left h, Complex.norm_real, Real.norm_of_nonneg (le_max_right _ _)]
      exact max_le ((sub_le_self _ (Nat.cast_nonneg n)).trans hx) (Nat.cast_nonneg _)
    · simp [w, h]
  have hz (S : Finset ℕ) : (z S).re = ∑ n ∈ S with cell n,
      (heckeLogDerivCoefficient (ideleClassNormTwist χ 0) n).re * max (x - n) 0 := by
    simp only [z, Complex.re_sum, Finset.sum_filter, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, mul_zero, sub_zero]
    refine sum_congr rfl fun n _ ↦ ?_
    by_cases hn : cell n <;> simp [w, hn]
  have h := heckeLogDerivCoefficient_sum_sub_sum_prime_le χ (T : ℝ) (fun n ↦ (w n : ℂ)) hw
  rw [Nat.floor_natCast, ← Nat.primesLE_eq_filter_Ioc_zero] at h
  change ‖z (Ioc 0 T) - z (Nat.primesLE T)‖ ≤ _ at h
  have htail := (Complex.abs_re_le_norm _).trans h
  calc
    _ = 4 * |(z (Ioc 0 T) - z (Nat.primesLE T)).re| := by
      rw [Complex.sub_re, hz, hz, quadraticPrimePowerCellRieszSum, quadraticPrimeCellRieszSum,
        ← mul_sub, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 4)]
    _ ≤ 4 * (Module.finrank ℚ F * (T : ℝ) * (21 * Real.sqrt T)) := by
      apply mul_le_mul_of_nonneg_left (htail.trans ?_) (by norm_num)
      exact mul_le_mul_of_nonneg_left (jacobiCell_psi_sub_theta_le T hT) (by positivity)
    _ = _ := by ring

/-- At a fourth-power cutoff, the real part of the prime Dirichlet row in
any of the four cells approximates the complete rational Hecke row with
absolute error at most `84 J^6`, uniformly in the conductor. -/
theorem rationalPrimitiveJacobiCell_complete_sub_prime (i : RationalPrimitiveCharacter)
    {J : ℕ} (hJ : 1 ≤ J) {x : ℝ} (hx : x ≤ (J : ℝ)^4) (u v : ℕ) (a b : Bool) :
    |quadraticPrimePowerCellRieszSum (rationalPrimitiveHeckeParameter i) (J^4) x u v
        (if a then 1 else -1) (if b then 1 else -1) -
      (4 * dirichletThetaRow i.2.1 ((Nat.primesLE (J^4)).filter (fun n ↦
        (jacobiSym u n : ℝ) = (if a then 1 else -1) ∧
        (jacobiSym v n : ℝ) = (if b then 1 else -1)))
        (fun n ↦ ((ArithmeticFunction.vonMangoldt n * max (x - n) 0 : ℝ) : ℂ))).re| ≤
      84 * (J : ℝ)^6 := by
  have h := quadraticPrimePowerCell_sub_prime_le_sqrt (rationalPrimitiveHeckeParameter i)
    (T := J^4) (one_le_pow₀ hJ) (by simpa only [Nat.cast_pow] using hx) u v
    (if a then 1 else -1) (if b then 1 else -1)
  have hs : Real.sqrt ((J : ℝ)^4) = (J : ℝ)^2 := by
    rw [show (J : ℝ)^4 = ((J : ℝ)^2)^2 by ring, Real.sqrt_sq (sq_nonneg _)]
  simp only [Module.finrank_self, Nat.cast_one, mul_one, Nat.cast_pow, hs] at h
  have he : (84 : ℝ) * J^4 * J^2 = 84 * J^6 := by ring
  rw [he] at h
  simpa only [quadraticPrimeCellRieszSum, dirichletThetaRow, Complex.re_sum, Complex.mul_re,
    (rationalPrimitiveHeckeParameter_spec i).2.2.2, Complex.ofReal_re, Complex.ofReal_im,
    Complex.re_ofNat, Complex.im_ofNat, mul_zero, zero_mul, sub_zero, mul_assoc] using h

end RiemannMasullo
