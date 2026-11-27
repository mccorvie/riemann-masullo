module

public import RiemannMasullo.ForMathlib.NumberTheory.LSeries.Selberg.Definitions
import RiemannMasullo.ForMathlib.NumberTheory.LSeries.Selberg.Arithmetic.CoprimeLogSum
import RiemannMasullo.ForMathlib.NumberTheory.LSeries.Selberg.Arithmetic.RowFactor
import RiemannMasullo.ForMathlib.NumberTheory.LSeries.Selberg.Arithmetic.SmoothPairBound

public section

namespace RiemannMasullo.Selberg

/-- Card 9. For r ≥ 1 and N ≥ 2, the absolute tapered row at power one is bounded by a constant
times `(smoothMass r)³ / (r log N)`.
Titchmarsh, §10.14, p. 273, inner row bound with a larger Euler product. -/
theorem row_bound : ∃ C > (0 : ℝ), ∀ N r : ℕ, 2 ≤ N → 0 < r →
    |row N (beta N) 1 r| ≤ C * (smoothMass r)^3 / (r * Real.log N) := by
  classical
  obtain ⟨C, hC, hsum⟩ := coprime_logSum
  refine ⟨3 * C^2, by positivity, fun N r hN hr ↦ ?_⟩
  have hNr : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hlog : 1 / 2 ≤ Real.log N := calc
    (1 : ℝ) / 2 = 1 - (2 : ℝ)⁻¹ := by norm_num
    _ ≤ Real.log 2 := Real.one_sub_inv_le_log_of_pos (by norm_num)
    _ ≤ Real.log N := Real.log_le_log (by norm_num) hNr
  have hlog_pos : 0 < Real.log N := by linarith
  have hmass : 0 ≤ smoothMass r := by
    apply Finset.prod_nonneg
    intro p hp
    have hp' : (1 : ℝ) < p := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).one_lt
    exact inv_nonneg.mpr (sub_nonneg.mpr (inv_lt_one_of_one_lt₀ hp').le)
  let B := C * smoothMass r * Real.sqrt (1 + Real.log N)
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hcut (d : ℕ) (hd : d ∈ D N) : |logSum r ((N : ℝ) / d)| ≤ B := by
    obtain ⟨hd₁, hdN⟩ := Finset.mem_Icc.mp hd
    have hd₁' : (1 : ℝ) ≤ d := by exact_mod_cast hd₁
    have hdN' : (d : ℝ) ≤ N := by exact_mod_cast hdN
    have hdpos : (0 : ℝ) < d := lt_of_lt_of_le zero_lt_one hd₁'
    have hlow : 1 ≤ (N : ℝ) / d := (one_le_div hdpos).mpr hdN'
    have hupp : (N : ℝ) / d ≤ N := div_le_self (Nat.cast_nonneg _) hd₁'
    exact (hsum r _ hr hlow).trans (mul_le_mul_of_nonneg_left
      (Real.sqrt_le_sqrt (add_le_add_right (Real.log_le_log (zero_lt_one.trans_le hlow) hupp) 1))
      (mul_nonneg hC.le hmass))
  have hBsq : B^2 = (C * smoothMass r)^2 * (1 + Real.log N) := by
    dsimp [B]
    rw [mul_pow, Real.sq_sqrt (by positivity)]
  rw [row_factor r N hr hN, abs_div, abs_of_nonneg (sq_nonneg (Real.log N))]
  calc
    _ ≤ (smoothMass r / r * B^2) / (Real.log N)^2 := by
      apply div_le_div_of_nonneg_right _ (sq_nonneg _)
      apply le_trans _ (mul_le_mul_of_nonneg_right (smooth_pair_bound r N hr) (sq_nonneg B))
      simp only [Finset.sum_mul]
      refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun d hd ↦ ?_)
      refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun e he ↦ ?_)
      have hde : 0 ≤ (d : ℝ) * e := by positivity
      rw [abs_mul, abs_mul, abs_div, abs_of_nonneg hde, mul_assoc, pow_two]
      exact mul_le_mul_of_nonneg_left (mul_le_mul (hcut d (Finset.mem_filter.mp hd).1)
        (hcut e (Finset.mem_filter.mp he).1) (abs_nonneg _) hB) (by positivity)
    _ ≤ (smoothMass r / r * ((C * smoothMass r)^2 * (3 * Real.log N))) / (Real.log N)^2 := by
      rw [hBsq]
      gcongr
      linarith
    _ = _ := by field_simp

end RiemannMasullo.Selberg
