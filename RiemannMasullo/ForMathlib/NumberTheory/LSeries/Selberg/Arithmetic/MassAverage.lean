module

public import RiemannMasullo.ForMathlib.NumberTheory.LSeries.Selberg.Definitions
import RiemannMasullo.ForMathlib.NumberTheory.LSeries.Selberg.Arithmetic.MassMajorant
import Mathlib.Analysis.PSeries
import Mathlib.NumberTheory.Harmonic.Bounds

public section

namespace RiemannMasullo.Selberg

/-- Writing each multiple of a divisor as `r = d * m` separates its two weights. -/
private theorem sum_divisor_weights (U : ℕ) :
    (∑ r ∈ D U, (∑ d ∈ r.divisors, (Real.sqrt d)⁻¹) / r) =
      ∑ d ∈ D U, ((d : ℝ) ^ (3 / 2 : ℝ))⁻¹ * ∑ m ∈ D (U / d), (m : ℝ)⁻¹ := by
  let f : ArithmeticFunction ℝ := ⟨fun d ↦ ((d : ℝ) ^ (3 / 2 : ℝ))⁻¹, by norm_num⟩
  let g : ArithmeticFunction ℝ := ⟨fun m ↦ (m : ℝ)⁻¹, by simp⟩
  refine Eq.trans ?_ (spectralLineJet_selberg_hyperbola_sum U f g)
  refine Finset.sum_congr rfl fun r _ ↦ ?_
  rw [Finset.sum_div, ArithmeticFunction.mul_apply,
    Nat.sum_divisorsAntidiagonal (fun d m ↦ f d * g m)]
  refine Finset.sum_congr rfl fun d hd ↦ ?_
  have hdvd := Nat.dvd_of_mem_divisors hd
  have hd0 : (d : ℝ) ≠ 0 := by exact_mod_cast (Nat.pos_of_mem_divisors hd).ne'
  have hprod : (d : ℝ) * ((r / d : ℕ) : ℝ) = r := by exact_mod_cast Nat.mul_div_cancel' hdvd
  change (Real.sqrt d)⁻¹ / r = ((d : ℝ) ^ (3 / 2 : ℝ))⁻¹ * ((r / d : ℕ) : ℝ)⁻¹
  rw [Real.sqrt_eq_rpow, show (3 / 2 : ℝ) = 1 / 2 + 1 by norm_num, Real.rpow_add_one hd0,
    div_eq_mul_inv, ← hprod, mul_inv_rev, mul_inv_rev]
  ring

/-- Card 13. The reciprocal-weighted sum of the sixth powers of the Euler products through U is
bounded by a constant times 1 + log U.
Titchmarsh, §10.14, pp. 273–274, divisor interchange. -/
theorem mass_average : ∃ C > (0 : ℝ), ∀ U : ℕ, 1 ≤ U →
    (∑ r ∈ D U, (smoothMass r)^6 / r) ≤ C * (1+Real.log U) := by
  obtain ⟨A, hA, hmaj⟩ := mass_majorant
  have hs := Real.summable_nat_rpow_inv.mpr (show 1 < (3 / 2 : ℝ) by norm_num)
  let S := ∑' d : ℕ, ((d : ℝ) ^ (3 / 2 : ℝ))⁻¹
  have hS : 0 < S := hs.tsum_pos (fun d ↦ by positivity) 1 (by norm_num)
  refine ⟨A * S, mul_pos hA hS, ?_⟩
  intro U hU
  have hharm (d : ℕ) : (∑ m ∈ D (U / d), (m : ℝ)⁻¹) ≤ 1 + Real.log U := by
    calc
      _ ≤ ∑ m ∈ D U, (m : ℝ)⁻¹ := Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.Icc_subset_Icc_right (Nat.div_le_self U d)) (fun _ _ _ ↦ by positivity)
      _ ≤ _ := by
        simpa only [D, harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]
          using harmonic_le_one_add_log U
  have hlog : 0 ≤ 1 + Real.log U :=
    add_nonneg zero_le_one (Real.log_nonneg (by exact_mod_cast hU))
  calc
    _ ≤ ∑ r ∈ D U, A * (∑ d ∈ r.divisors, (Real.sqrt d)⁻¹) / r :=
      Finset.sum_le_sum fun r hr ↦ div_le_div_of_nonneg_right
        (hmaj r (Finset.mem_Icc.mp hr).1) (Nat.cast_nonneg _)
    _ = A * ∑ d ∈ D U, ((d : ℝ) ^ (3 / 2 : ℝ))⁻¹ *
          ∑ m ∈ D (U / d), (m : ℝ)⁻¹ := by
      simp_rw [mul_div_assoc]
      rw [← Finset.mul_sum, sum_divisor_weights]
    _ ≤ A * ∑ d ∈ D U, ((d : ℝ) ^ (3 / 2 : ℝ))⁻¹ * (1 + Real.log U) := by
      gcongr with d
      exact hharm d
    _ ≤ _ := by
      rw [← Finset.sum_mul, ← mul_assoc]
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
        (hs.sum_le_tsum _ (fun _ _ ↦ by positivity)) hA.le) hlog

end RiemannMasullo.Selberg
