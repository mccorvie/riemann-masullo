module

public import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.NumberTheory.DiophantineApproximation.Basic
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-! # Quantitative density of powers on the unit circle

A polynomial lower bound for returns to the identity gives a polynomial upper bound for
the time to reach any target arc. Dirichlet's rational approximation supplies a reduced
fraction whose denominator is large by the return estimate. Its multiples visit an entire
uniform grid before the denominator, and each true orbit point stays close to its grid point.
-/

public noncomputable section

namespace Circle

open Real

private def turn (x : ℝ) : Circle := Circle.exp (2 * π * x)

private theorem turn_arg (a : Circle) : turn (Complex.arg (a : ℂ) / (2 * π)) = a := by
  rw [turn, show 2 * π * (Complex.arg (a : ℂ) / (2 * π)) = Complex.arg (a : ℂ) by field_simp,
    Circle.exp_arg]

private theorem turn_sub_int (x : ℝ) (m : ℤ) : turn (x - m) = turn x := by
  simp [turn, mul_sub, Circle.exp_sub, Circle.exp_two_pi_mul_int]

private theorem turn_zpow (x : ℝ) (k : ℤ) : turn ((k : ℝ) * x) = turn x ^ k := by
  simpa only [turn, zsmul_eq_mul, mul_left_comm] using Circle.exp_zsmul (2 * π * x) k

private theorem turn_natPow (x : ℝ) (k : ℕ) : turn ((k : ℝ) * x) = turn x ^ k := by
  simpa using turn_zpow x (k : ℤ)

private theorem turn_distance (x y : ℝ) (j : ℤ) :
    ‖(turn x : ℂ) - turn y‖ ≤ 2 * π * |x - y - j| := by
  have hdiv : turn (x - y - j) = turn x / turn y := by
    rw [turn_sub_int]
    simp [turn, mul_sub]
  have heq : (turn x : ℂ) - turn y =
      ((turn (x - y - j) : ℂ) - 1) * (turn y : ℂ) := by
    rw [hdiv, Circle.coe_div, sub_mul, div_mul_cancel₀ _ (Circle.coe_ne_zero _), one_mul]
  rw [heq, norm_mul, Circle.norm_coe, mul_one]
  have h := Real.norm_exp_I_mul_ofReal_sub_one_le (x := 2 * π * (x - y - j))
  rw [turn, Circle.coe_exp, mul_comm _ Complex.I]
  simpa [Real.norm_eq_abs, abs_of_pos Real.pi_pos, abs_mul] using h

/-- Every residue on the grid of a reduced rational is reached before the denominator. -/
private theorem rat_grid (r : ℚ) (u : ℤ) :
    ∃ k j : ℤ, 0 ≤ k ∧ k < r.den ∧ k * r.num - u = j * r.den := by
  obtain ⟨a, b, hab⟩ := r.isCoprime_num_den
  let k := (a * u) % (r.den : ℤ)
  have hpos : (0 : ℤ) < r.den := by exact_mod_cast r.den_pos
  refine ⟨k, -((a * u) / (r.den : ℤ)) * r.num - b * u, Int.emod_nonneg _ (ne_of_gt hpos),
    Int.emod_lt_of_pos _ hpos, ?_⟩
  have hid := Int.emod_add_mul_ediv (a * u) (r.den : ℤ)
  dsimp [k]
  linear_combination r.num * hid + u * hab

private theorem rat_angular_grid (r : ℚ) (x y : ℝ) :
    ∃ k j : ℤ, 0 ≤ k ∧ k < r.den ∧
      |(k : ℝ) * x - y - j| ≤ (r.den : ℝ) * |x - r| + 1 / (2 * r.den) := by
  let u := round ((r.den : ℝ) * y)
  obtain ⟨k, j, hk, hkr, h⟩ := rat_grid r u
  refine ⟨k, j, hk, hkr, ?_⟩
  have hr : (0 : ℝ) < r.den := by exact_mod_cast r.den_pos
  have h' : (k : ℝ) * (r.num : ℝ) - (u : ℝ) = (j : ℝ) * (r.den : ℝ) := by exact_mod_cast h
  have hg : (k : ℝ) * (r : ℝ) - j - y = ((u : ℝ) - (r.den : ℝ) * y) / (r.den : ℝ) := by
    rw [Rat.cast_def]
    field_simp
    linarith
  have hu : |(u : ℝ) - (r.den : ℝ) * y| ≤ 1 / 2 := by
    rw [abs_sub_comm]
    exact abs_sub_round _
  calc
    _ = |(k : ℝ) * (x - r) + ((k : ℝ) * (r : ℝ) - j - y)| := by ring_nf
    _ ≤ |(k : ℝ) * (x - r)| + |(k : ℝ) * (r : ℝ) - j - y| := abs_add_le _ _
    _ ≤ _ := by
      rw [hg, abs_div, abs_of_pos hr, abs_mul, abs_of_nonneg (by exact_mod_cast hk : 0 ≤ (k : ℝ))]
      apply add_le_add
      · gcongr
        exact_mod_cast hkr.le
      · rw [← div_div]
        exact div_le_div_of_nonneg_right hu hr.le

/-- A homogeneous lower bound for powers gives a polynomial covering time of the same
degree for every inhomogeneous target, uniformly over the starting exponent. -/
theorem exists_zpow_approx_of_separation (a : Circle) (C : ℝ) (d : ℕ)
    (hsep : ∀ n : ℕ, 0 < n → C / (1 + (n : ℝ)) ^ d ≤ ‖(a : ℂ) ^ n - 1‖)
    {N Q : ℕ} (hN : 0 < N) (hQ : 0 < Q)
    (hsize : 2 * π * (1 + (N : ℝ)) ^ d < C * ((Q : ℝ) + 1)) (K : ℤ) (b : Circle) :
    ∃ k : ℤ, K ≤ k ∧ k < K + Q ∧ ‖(a : ℂ) ^ k - b‖ ≤ 3 * π / N := by
  let x := Complex.arg (a : ℂ) / (2 * π)
  let y := Complex.arg (b : ℂ) / (2 * π) - (K : ℝ) * x
  have ha : turn x = a := turn_arg a
  have hb : turn (y + (K : ℝ) * x) = b := by
    simpa only [y, sub_add_cancel] using turn_arg b
  obtain ⟨r, hr, hden⟩ := Real.exists_rat_abs_sub_le_and_den_le x hQ
  have hpos : (0 : ℝ) < r.den := by exact_mod_cast r.den_pos
  have hQpos : 0 < (Q : ℝ) + 1 := by positivity
  have hfrac : (r.den : ℝ) * |x - r| ≤ 1 / ((Q : ℝ) + 1) := by
    calc
      _ ≤ (r.den : ℝ) * (1 / (((Q : ℝ) + 1) * r.den)) := by gcongr
      _ = _ := by field_simp
  have hdenlt : N < r.den := by
    by_contra! hle
    have hg : |(r.den : ℝ) * x - 0 - (r.num : ℝ)| = (r.den : ℝ) * |x - r| := by
      rw [← abs_of_pos hpos, ← abs_mul, Rat.cast_def, mul_sub]
      field_simp
      simp [abs_of_pos hpos, mul_comm]
    have hs := turn_distance ((r.den : ℝ) * x) 0 r.num
    rw [hg, turn_natPow, ha, show turn 0 = 1 by simp [turn], Circle.coe_pow, Circle.coe_one] at hs
    have hbnd := (hsep r.den r.den_pos).trans
      (hs.trans (mul_le_mul_of_nonneg_left hfrac (by positivity)))
    have hc : C * ((Q : ℝ) + 1) ≤ 2 * π * (1 + (r.den : ℝ)) ^ d := by
      rw [← mul_div_assoc, mul_one] at hbnd
      exact (div_le_div_iff₀ (by positivity) hQpos).mp hbnd
    have hpow : 2 * π * (1 + (r.den : ℝ)) ^ d ≤ 2 * π * (1 + (N : ℝ)) ^ d := by gcongr
    linarith
  obtain ⟨k, j, hk, hkd, hgrid⟩ := rat_angular_grid r x y
  refine ⟨K + k, by omega, by omega, ?_⟩
  have hh := turn_distance (((K + k : ℤ) : ℝ) * x) (y + (K : ℝ) * x) j
  rw [turn_zpow, ha, Circle.coe_zpow, hb] at hh
  have hcancel : (((K + k : ℤ) : ℝ) * x) - (y + (K : ℝ) * x) - (j : ℝ) = (k : ℝ) * x - y - j := by
    push_cast
    ring
  rw [hcancel] at hh
  have hNr : (N : ℝ) ≤ r.den := by exact_mod_cast hdenlt.le
  have hNQ : (N : ℝ) ≤ (Q : ℝ) + 1 := by
    have : N ≤ Q := hdenlt.le.trans hden
    exact_mod_cast (by omega : N ≤ Q + 1)
  calc
    _ ≤ 2 * π * ((r.den : ℝ) * |x - r| + 1 / (2 * r.den)) :=
      hh.trans (mul_le_mul_of_nonneg_left hgrid (by positivity))
    _ ≤ 2 * π * (1 / (N : ℝ) + 1 / (2 * N)) := by
      gcongr
      · exact hfrac.trans (by gcongr)
    _ = _ := by ring

/-- Dirichlet returns to the identity give a chord at most `2π/k` at unbounded
positive powers. The separation hypothesis guarantees the chosen powers escape every cutoff. -/
theorem exists_large_pow_return_of_separation (a : Circle) {C : ℝ} (hC : 0 < C) {d : ℕ}
    (hsep : ∀ n : ℕ, 0 < n → C / (1 + (n : ℝ)) ^ d ≤ ‖(a : ℂ) ^ n - 1‖) (M : ℕ) :
    ∃ k : ℕ, M < k ∧ 0 < ‖(a : ℂ) ^ k - 1‖ ∧ ‖(a : ℂ) ^ k - 1‖ ≤ 2 * π / k := by
  obtain ⟨Q, hQ⟩ := exists_nat_gt (2 * π * (1 + (M : ℝ)) ^ d / C)
  have hQpos : 0 < Q := by exact_mod_cast (lt_trans (by positivity) hQ : (0 : ℝ) < Q)
  let x := Complex.arg (a : ℂ) / (2 * π)
  have ha : turn x = a := turn_arg a
  obtain ⟨k, hk, hkQ, hr⟩ := Real.exists_nat_abs_mul_sub_round_le x hQpos
  have hh := turn_distance ((k : ℝ) * x) 0 (round ((k : ℝ) * x))
  rw [turn_natPow, ha, show turn 0 = 1 by simp [turn], Circle.coe_pow, Circle.coe_one, sub_zero] at hh
  have hb : ‖(a : ℂ) ^ k - 1‖ ≤ 2 * π / ((Q : ℝ) + 1) := by
    simpa [div_eq_mul_inv] using hh.trans (mul_le_mul_of_nonneg_left hr (by positivity : 0 ≤ 2 * π))
  have hkM : M < k := by
    by_contra! hle
    have hh := (div_le_div_iff₀ (by positivity) (by positivity)).mp ((hsep k hk).trans hb)
    have hpow : 2 * π * (1 + (k : ℝ)) ^ d ≤ 2 * π * (1 + (M : ℝ)) ^ d := by gcongr
    have hlarge := (div_lt_iff₀ hC).mp hQ
    nlinarith only [hh, hpow, hlarge, hC]
  refine ⟨k, hkM, (show 0 < C / (1 + (k : ℝ)) ^ d by positivity).trans_le (hsep k hk), hb.trans ?_⟩
  have hk' : (k : ℝ) ≤ Q := by exact_mod_cast hkQ
  gcongr
  linarith

end Circle
