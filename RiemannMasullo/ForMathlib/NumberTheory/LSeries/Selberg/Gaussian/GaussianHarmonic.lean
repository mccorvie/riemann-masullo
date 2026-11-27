module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.PSeries

public section

namespace RiemannMasullo.Selberg

private lemma exp_neg_le_inv_eighth {z : ℝ} (hz : 0 < z) :
    Real.exp (-z) ≤ z⁻¹ ^ (1 / 8 : ℝ) := by
  rw [Real.rpow_def_of_pos (inv_pos.mpr hz), Real.log_inv, Real.exp_le_exp]
  linarith [Real.log_le_sub_one_of_pos hz]

private lemma gaussian_harmonic_term_le {u N : ℝ} (hu : 1 ≤ u) (hN : 1 ≤ N) :
    Real.exp (-u ^ 2 / (2 * N ^ 102)) * (1 + Real.log (u * N ^ 2)) / u ≤
      (9 * (2 : ℝ) ^ (1 / 8 : ℝ) * N ^ 13) * u ^ (-9 / 8 : ℝ) := by
  have hu₀ : 0 < u := zero_lt_one.trans_le hu
  have hN₀ : 0 < N := zero_lt_one.trans_le hN
  have hw : 1 ≤ u * N ^ 2 := one_le_mul_of_one_le_of_one_le hu (one_le_pow₀ hN)
  have hlog : 1 + Real.log (u * N ^ 2) ≤ 9 * (u * N ^ 2) ^ (1 / 8 : ℝ) := by
    linarith [Real.log_le_rpow_div (zero_le_one.trans hw) (by norm_num : (0 : ℝ) < 1 / 8),
      Real.one_le_rpow hw (by norm_num : (0 : ℝ) ≤ 1 / 8)]
  have hexp : Real.exp (-u ^ 2 / (2 * N ^ 102)) ≤ (2 * N ^ 102 / u ^ 2) ^ (1 / 8 : ℝ) := by
    simpa only [neg_div, inv_div] using
      exp_neg_le_inv_eighth (show 0 < u ^ 2 / (2 * N ^ 102) by positivity)
  calc
    _ ≤ ((2 * N ^ 102 / u ^ 2) ^ (1 / 8 : ℝ) * (9 * (u * N ^ 2) ^ (1 / 8 : ℝ))) / u := by
      gcongr
      exact add_nonneg zero_le_one (Real.log_nonneg hw)
    _ = 9 * (2 * N ^ 104 / u) ^ (1 / 8 : ℝ) / u := by
      have h : 2 * N ^ 104 / u = (2 * N ^ 102 / u ^ 2) * (u * N ^ 2) := by
        field_simp
      rw [h, Real.mul_rpow (x := 2 * N ^ 102 / u ^ 2) (by positivity) (by positivity)]
      ring
    _ = _ := by
      rw [Real.div_rpow (by positivity) hu₀.le, Real.mul_rpow (by norm_num) (by positivity),
        ← Real.rpow_natCast_mul hN₀.le, show ((104 : ℕ) : ℝ) * (1 / 8) = 13 by norm_num,
        show (-9 / 8 : ℝ) = -(1 / 8) - 1 by norm_num, Real.rpow_sub_one hu₀.ne',
        Real.rpow_neg hu₀.le]
      norm_num
      ring

/-- Card 32. The Gaussian-damped harmonic series with its logarithmic weight converges and is
bounded by a constant times N¹⁴ for N ≥ 2.
Coarse specialization of Titchmarsh §10.16, p. 275, before (10.16.1). -/
theorem gaussian_harmonic : ∃ C > (0 : ℝ), ∀ N : ℕ, 2 ≤ N →
    let term := fun i : ℕ ↦ let u : ℝ := (i : ℝ)+1
      Real.exp (-u^2/(2*(N : ℝ)^102)) * (1+Real.log (u*N^2))/u
    Summable term ∧ ∑' i, term i ≤ C*(N : ℝ)^14 := by
  let p : ℕ → ℝ := fun i ↦ ((i : ℝ) + 1) ^ (-9 / 8 : ℝ)
  have hp : Summable p := by
    simpa only [p, Nat.cast_add, Nat.cast_one] using
      (summable_nat_add_iff 1).2 (Real.summable_nat_rpow.mpr (by norm_num : (-9 / 8 : ℝ) < -1))
  have hp_pos : ∀ i, 0 < p i := fun i ↦ Real.rpow_pos_of_pos (by positivity) _
  let K := 9 * (2 : ℝ) ^ (1 / 8 : ℝ)
  have hC : 0 < K * ∑' i, p i := mul_pos (by positivity [K])
    (hp.tsum_pos (fun i ↦ (hp_pos i).le) 0 (hp_pos 0))
  refine ⟨_, hC, ?_⟩
  intro N hN
  dsimp only
  have hN₁ : 1 ≤ (N : ℝ) := by exact_mod_cast (by omega : 1 ≤ N)
  have hu (i : ℕ) : 1 ≤ (i : ℝ) + 1 := by simp
  have hle := fun i : ℕ ↦ gaussian_harmonic_term_le (hu i) hN₁
  have hmajor := hp.mul_left (K * (N : ℝ) ^ 13)
  have hsum := Summable.of_nonneg_of_le (fun i ↦ by
    have hw : 1 ≤ ((i : ℝ) + 1) * (N : ℝ) ^ 2 :=
      one_le_mul_of_one_le_of_one_le (hu i) (one_le_pow₀ hN₁)
    have := Real.log_nonneg hw
    positivity) hle hmajor
  refine ⟨hsum, (hsum.tsum_le_tsum hle hmajor).trans ?_⟩
  calc
    _ = (K * ∑' i, p i) * (N : ℝ) ^ 13 := by rw [hp.tsum_mul_left]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hN₁ (by decide : 13 ≤ 14)) hC.le

end RiemannMasullo.Selberg
