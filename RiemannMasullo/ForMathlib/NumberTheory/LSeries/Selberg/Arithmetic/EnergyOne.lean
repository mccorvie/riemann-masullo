module

public import RiemannMasullo.ForMathlib.NumberTheory.LSeries.Selberg.Definitions
import RiemannMasullo.ForMathlib.NumberTheory.LSeries.Selberg.Arithmetic.EnergyRows
import RiemannMasullo.ForMathlib.NumberTheory.LSeries.Selberg.Arithmetic.JordanSum
import RiemannMasullo.ForMathlib.NumberTheory.LSeries.Selberg.Arithmetic.MassAverage
import RiemannMasullo.ForMathlib.NumberTheory.LSeries.Selberg.Arithmetic.RowBound

public section

namespace RiemannMasullo.Selberg

/-- Card 14. For N ≥ 2 the tapered energy at power one is bounded above by a constant times 1 /
log N.
Titchmarsh, Lemma 10.14, pp. 273–274, S(0). -/
theorem energy_one : ∃ C > (0 : ℝ), ∀ N : ℕ, 2 ≤ N →
    energy N (beta N) 1 ≤ C / Real.log N := by
  obtain ⟨A, hA, hrow⟩ := row_bound
  obtain ⟨B, hB, hmass⟩ := mass_average
  refine ⟨A ^ 2 * B * 4, by positivity, ?_⟩
  intro N hN
  have hlog : 1 / 2 ≤ Real.log N := calc
    (1 : ℝ) / 2 ≤ Real.log 2 := by
      convert Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2) using 1
      norm_num
    _ ≤ Real.log N := Real.log_le_log (by norm_num) (by exact_mod_cast hN)
  have hlog_pos : 0 < Real.log N := by linarith
  have hlog_sq : 1 + Real.log ((N * N : ℕ) : ℝ) ≤ 4 * Real.log N := by
    rw [Nat.cast_mul, ← sq, Real.log_pow]
    push_cast
    linarith
  rw [energy_rows N (beta N) 1 zero_lt_one]
  calc
    _ ≤ ∑ r ∈ D (N * N), (A ^ 2 / (Real.log N) ^ 2) * (smoothMass r ^ 6 / r) := by
      refine Finset.sum_le_sum fun r hr ↦ ?_
      have hr_nat : 0 < r := (Finset.mem_Icc.mp hr).1
      have hr_pos : 0 < (r : ℝ) := by exact_mod_cast hr_nat
      have hj : jordan 1 r ≤ r := by
        simpa only [Real.rpow_one] using (jordan_sum 1 zero_lt_one r hr_nat).2.2
      have hs := hrow N r hN hr_nat
      calc
        _ ≤ (r : ℝ) * (row N (beta N) 1 r) ^ 2 :=
          mul_le_mul_of_nonneg_right hj (sq_nonneg _)
        _ ≤ (r : ℝ) * (A * smoothMass r ^ 3 / (r * Real.log N)) ^ 2 :=
          mul_le_mul_of_nonneg_left (sq_le_sq.mpr (hs.trans (le_abs_self _))) hr_pos.le
        _ = _ := by field_simp
    _ ≤ A ^ 2 / (Real.log N) ^ 2 * (B * (4 * Real.log N)) := by
      rw [← Finset.mul_sum]
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact (hmass (N * N) (Nat.mul_pos (by omega) (by omega))).trans
        (mul_le_mul_of_nonneg_left hlog_sq hB.le)
    _ = _ := by field_simp

end RiemannMasullo.Selberg
