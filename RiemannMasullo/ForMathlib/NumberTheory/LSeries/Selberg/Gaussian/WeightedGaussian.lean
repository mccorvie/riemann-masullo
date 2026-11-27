module

public import RiemannMasullo.ForMathlib.NumberTheory.LSeries.Selberg.Definitions
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import RiemannMasullo.ForMathlib.NumberTheory.LSeries.Selberg.Arithmetic.EnergyOne
import RiemannMasullo.ForMathlib.NumberTheory.LSeries.Selberg.Arithmetic.TaperSpec
import RiemannMasullo.ForMathlib.NumberTheory.LSeries.Selberg.Gaussian.DiagonalUpper
import RiemannMasullo.ForMathlib.NumberTheory.LSeries.Selberg.Gaussian.OffDiagonal

public section

namespace RiemannMasullo.Selberg

private lemma inv_pow_le_scale (N : ℕ) (hN : 1 ≤ (N : ℝ)) :
    1 / (N : ℝ)^50 ≤ scale N := by
  have hδ : 1 / (N : ℝ)^100 ≤ 1 := div_le_self zero_le_one (one_le_pow₀ hN)
  have hsin := Real.mul_le_sin (x := 1 / (N : ℝ)^100) (by positivity)
    (by linarith [Real.two_le_pi])
  unfold scale H
  rw [Nat.cast_pow]
  apply Real.le_sqrt_of_sq_le
  calc
    (1 / (N : ℝ)^50)^2 = 1 / (N : ℝ)^100 := by rw [div_pow, ← pow_mul]; norm_num
    _ ≤ 4 / (N : ℝ)^100 := by gcongr; norm_num
    _ = 2 * Real.pi * (2 / Real.pi * (1 / (N : ℝ)^100)) := by
      field_simp [Real.pi_ne_zero]
      norm_num
    _ ≤ _ := mul_le_mul_of_nonneg_left hsin (by positivity)

/-- Card 34. For the taper and 0 < q ≤ 1/2, the weighted Gaussian integral J is bounded above by a
constant times N⁵⁰/(q log N).
Titchmarsh, (10.17.2), p. 275, needed only at x=1. -/
theorem weighted_gaussian : ∃ C > (0 : ℝ), ∀ N : ℕ, 2 ≤ N → ∀ q : ℝ,
    0 < q → q ≤ 1/2 → J N (beta N) q ≤ C*(N : ℝ)^50/(q*Real.log N) := by
  obtain ⟨A, hA, henergy⟩ := energy_one
  obtain ⟨B, hB, hoff⟩ := off_diagonal
  have hg : 0 < gaussC := by unfold gaussC; positivity
  refine ⟨gaussC * A + 2 + B, by positivity, ?_⟩
  intro N hN q hq hq'
  have hN₁ : 1 < (N : ℝ) := by exact_mod_cast (show 1 < N from hN)
  have hN₀ : 0 < (N : ℝ) := zero_lt_one.trans hN₁
  have hlog := Real.log_pos hN₁
  let M := (N : ℝ)^50 / (q * Real.log N)
  have hmain : gaussC * energy N (beta N) 1 / (q * scale N) ≤ gaussC * A * M := calc
    _ ≤ gaussC * (A / Real.log N) / (q * (1 / (N : ℝ)^50)) :=
      div_le_div₀ (by positivity) (mul_le_mul_of_nonneg_left (henergy N hN) hg.le)
        (by positivity) (mul_le_mul_of_nonneg_left (inv_pow_le_scale N hN₁.le) hq.le)
    _ = _ := by dsimp [M]; field_simp
  have hqlog : q * Real.log N ≤ N :=
    (mul_le_of_le_one_left hlog.le (by linarith)).trans (Real.log_le_self hN₀.le)
  have herr (k : ℕ) (hk : k + 1 ≤ 50) : (N : ℝ)^k ≤ M := by
    apply (le_div_iff₀ (mul_pos hq hlog)).2
    calc
      _ ≤ (N : ℝ)^k * N := mul_le_mul_of_nonneg_left hqlog (by positivity)
      _ = (N : ℝ)^(k + 1) := (pow_succ _ _).symm
      _ ≤ _ := pow_le_pow_right₀ hN₁.le hk
  have hb := (taper_spec N hN).2
  have hd := diagonal_upper N hN (beta N) hb q hq hq'
  have ho := (le_abs_self _).trans (hoff N hN (beta N) hb q hq.le)
  calc
    J N (beta N) q ≤ gaussC * energy N (beta N) 1 / (q * scale N) +
        2 * (N : ℝ)^4 + B * (N : ℝ)^22 := by linarith only [hd, ho]
    _ ≤ gaussC * A * M + 2 * M + B * M :=
      add_le_add (add_le_add hmain (mul_le_mul_of_nonneg_left (herr 4 (by decide)) (by norm_num)))
        (mul_le_mul_of_nonneg_left (herr 22 (by decide)) hB.le)
    _ = _ := by dsimp [M]; ring

end RiemannMasullo.Selberg
