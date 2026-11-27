module

public import RiemannMasullo.ForMathlib.NumberTheory.LSeries.Selberg.Definitions

public section

namespace RiemannMasullo.Selberg

/-- Card 1. For N ≥ 2 the logarithmic taper has first coefficient one, and its coefficients
through N have absolute value at most one.
Titchmarsh, §10.9, pp. 268–269. -/
theorem taper_spec (N : ℕ) (hN : 2 ≤ N) :
    beta N 1 = 1 ∧ bd N (beta N) := by
  have hN_real : 1 < (N : ℝ) := by exact_mod_cast (show 1 < N from hN)
  have hlog : 0 < Real.log N := Real.log_pos hN_real
  obtain ⟨halpha_one, halpha_bound, _⟩ := spectralLineJet_selbergHalfMoebius_spec
  constructor
  · have hone : 1 ∈ D N := Finset.mem_Icc.mpr ⟨le_rfl, Nat.le_of_lt hN⟩
    simp [beta, hone, alpha, halpha_one, hlog.ne']
  · intro n hn
    obtain ⟨hn_one, hnN⟩ := Finset.mem_Icc.mp hn
    have hn_real : 1 ≤ (n : ℝ) := by exact_mod_cast hn_one
    have hn_pos : 0 < (n : ℝ) := zero_lt_one.trans_le hn_real
    have hquot : 1 ≤ (N : ℝ) / n := (one_le_div hn_pos).mpr (by exact_mod_cast hnN)
    have hnonneg := div_nonneg (Real.log_nonneg hquot) hlog.le
    have hle := Real.log_le_log (zero_lt_one.trans_le hquot)
      (div_le_self (zero_le_one.trans hN_real.le) hn_real)
    rw [beta, ite_eq_left hn, abs_mul, abs_of_nonneg hnonneg]
    exact (mul_le_of_le_one_left hnonneg (halpha_bound n)).trans ((div_le_one hlog).mpr hle)

end RiemannMasullo.Selberg
