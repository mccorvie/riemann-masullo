module

public import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds

/-! # Lower bound for a separated exponential factor -/

public section

namespace RiemannMasullo

/-- Away from its roots, the exponential factor `1 - θ exp (-L z)` is bounded below by a
constant times the separation radius, uniformly in the complex coefficient and the center. -/
theorem exists_mul_le_norm_one_sub_mul_exp_of_separated (L : ℝ) (hL : 0 < L) :
    ∃ c > (0 : ℝ), ∀ (θ z : ℂ) (r : ℝ), 0 < r → r ≤ 1 →
      (∀ b : ℂ, θ * Complex.exp (-(L : ℂ) * b) = 1 → r ≤ ‖z - b‖) →
      c * r ≤ ‖1 - θ * Complex.exp (-(L : ℂ) * z)‖ := by
  refine ⟨min (1 / 2) (2 * L / 3), lt_min (by norm_num) (by positivity), ?_⟩
  intro θ z r hr hr₁ hsep
  let y := θ * Complex.exp (-(L : ℂ) * z)
  change min (1 / 2) (2 * L / 3) * r ≤ ‖1 - y‖
  by_cases hfar : 1 / 2 ≤ ‖1 - y‖
  · calc
      _ ≤ (1 / 2 : ℝ) * r := mul_le_mul_of_nonneg_right (min_le_left _ _) hr.le
      _ ≤ 1 / 2 := mul_le_of_le_one_right (by norm_num) hr₁
      _ ≤ _ := hfar
  have hclose : ‖y - 1‖ ≤ 1 / 2 := by
    rw [norm_sub_rev]
    exact (lt_of_not_ge hfar).le
  have hy : y ≠ 0 := by
    intro heq
    rw [heq] at hclose
    norm_num at hclose
  have hlog : ‖Complex.log y‖ ≤ (3 / 2) * ‖1 - y‖ := by
    have h := Complex.norm_log_one_add_half_le_self hclose
    rw [show 1 + (y - 1) = y by ring, norm_sub_rev y 1] at h
    exact h
  let b := z + Complex.log y / (L : ℂ)
  have hL₀ : (L : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hL.ne'
  have hroot : θ * Complex.exp (-(L : ℂ) * b) = 1 := by
    have harg : -(L : ℂ) * b = -(L : ℂ) * z - Complex.log y := by
      calc
        _ = -(L : ℂ) * z - (Complex.log y / (L : ℂ)) * L := by dsimp only [b]; ring
        _ = _ := by rw [div_mul_cancel₀ _ hL₀]
    rw [harg, Complex.exp_sub, Complex.exp_log hy, ← mul_div_assoc]
    exact div_self hy
  have hdist : ‖z - b‖ = ‖Complex.log y‖ / L := by
    rw [show z - b = -(Complex.log y / (L : ℂ)) by dsimp only [b]; abel,
      norm_neg, norm_div, Complex.norm_real, Real.norm_of_nonneg hL.le]
  have hsep' := hsep b hroot
  rw [hdist] at hsep'
  calc
    _ ≤ (2 * L / 3) * r := mul_le_mul_of_nonneg_right (min_le_right _ _) hr.le
    _ ≤ _ := by nlinarith only [(le_div_iff₀ hL).mp hsep', hlog]

end RiemannMasullo
