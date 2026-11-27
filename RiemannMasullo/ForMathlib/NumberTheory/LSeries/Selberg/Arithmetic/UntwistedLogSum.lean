module

public import RiemannMasullo.ForMathlib.NumberTheory.LSeries.Selberg.Definitions

public section

namespace RiemannMasullo.Selberg

-- On a single unit interval the two square roots differ by at most a factor of two.
private theorem log_increment_le {x y : ℝ} (hx : 1 ≤ x) (hxy : x ≤ y) (hy : y ≤ x + 1) :
    (Real.log y - Real.log x) / Real.sqrt (1 + Real.log x) ≤
      3 * (Real.sqrt (1 + Real.log y) - Real.sqrt (1 + Real.log x)) := by
  have hx₀ := lt_of_lt_of_le zero_lt_one hx
  have hy₀ := hx₀.trans_le hxy
  have hlog := Real.log_nonneg hx
  have hmono := Real.log_le_log hx₀ hxy
  have hroot := Real.sqrt_le_sqrt (add_le_add (le_refl (1 : ℝ)) hmono)
  have hsx := Real.sq_sqrt (show 0 ≤ 1 + Real.log x by linarith)
  have hsy := Real.sq_sqrt (show 0 ≤ 1 + Real.log y by linarith)
  have hlog₂ := Real.log_le_log hy₀ (show y ≤ 2 * x by linarith)
  rw [Real.log_mul (by norm_num) hx₀.ne'] at hlog₂
  have hdouble : Real.sqrt (1 + Real.log y) ≤ 2 * Real.sqrt (1 + Real.log x) := by
    apply Real.sqrt_le_iff.mpr ⟨by positivity, ?_⟩
    nlinarith only [hsx, hlog₂, hlog, Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)]
  apply (div_le_iff₀ (Real.sqrt_pos.mpr (by linarith))).mpr
  nlinarith only [hsx, hsy, mul_nonneg (sub_nonneg.mpr hroot) (sub_nonneg.mpr hdouble)]

/-- Card 2. The logarithmically weighted sum of the untwisted half-Möbius coefficients through Y
is bounded in absolute value by a constant times √(1 + log Y) for Y ≥ 1.
Replacement for Titchmarsh (10.12.1), pp. 271–272, θ=0. -/
theorem untwisted_logSum : ∃ C > (0 : ℝ), ∀ Y : ℝ, 1 ≤ Y →
    |logSum 1 Y| ≤ C * Real.sqrt (1 + Real.log Y) := by
  obtain ⟨C, hC, hsum⟩ := spectralLineJet_selbergHalfMoebius_reciprocal_sum
  let a (n : ℕ) := alpha n / n
  let W (m : ℕ) (y : ℝ) := ∑ n ∈ Finset.Icc 1 m, a n * (Real.log y - Real.log n)
  -- Carry the bound across [m, m+1]. At the left endpoint the new summand vanishes.
  have bound (m : ℕ) (y : ℝ) (hm : (m : ℝ) ≤ y) (hy : y ≤ m + 1) :
      |W m y| ≤ 3 * C * Real.sqrt (1 + Real.log y) := by
    induction m generalizing y with
    | zero =>
      simp [W]
      positivity
    | succ m ih =>
      let x : ℝ := (m + 1 : ℕ)
      have hx : 1 ≤ x := by dsimp [x]; exact_mod_cast Nat.succ_pos m
      have hxy : x ≤ y := hm
      have hstart : W (m + 1) x = W m x := by
        simp [W, Finset.sum_Icc_succ_top (Nat.succ_pos m), x]
      have hprev : |W m x| ≤ 3 * C * Real.sqrt (1 + Real.log x) :=
        ih x (by simp [x]) (by simp [x])
      let S := ∑ n ∈ Finset.Icc 1 (m + 1), a n
      have hstep : W (m + 1) y = W (m + 1) x + S * (Real.log y - Real.log x) := by
        dsimp only [W, S]
        rw [Finset.sum_mul, ← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun n _ ↦ by ring
      have hS : |S| ≤ C / Real.sqrt (1 + Real.log x) := hsum (m + 1) (Nat.succ_pos m)
      have hdiff := sub_nonneg.mpr (Real.log_le_log (zero_lt_one.trans_le hx) hxy)
      have hinc : |S * (Real.log y - Real.log x)| ≤
          C * (3 * (Real.sqrt (1 + Real.log y) - Real.sqrt (1 + Real.log x))) := by
        rw [abs_mul, abs_of_nonneg hdiff]
        calc
          _ ≤ C / Real.sqrt (1 + Real.log x) * (Real.log y - Real.log x) :=
            mul_le_mul_of_nonneg_right hS hdiff
          _ = C * ((Real.log y - Real.log x) / Real.sqrt (1 + Real.log x)) := by ring
          _ ≤ _ := mul_le_mul_of_nonneg_left (log_increment_le hx hxy hy) hC.le
      rw [hstep, hstart]
      exact (abs_add_le ..).trans ((add_le_add hprev hinc).trans_eq (by ring))
  refine ⟨3 * C, by positivity, ?_⟩
  intro Y hY
  have heq : logSum 1 Y = W ⌊Y⌋₊ Y := by
    unfold logSum D W
    rw [Finset.filter_true_of_mem (fun n _ ↦ Nat.coprime_one_left n)]
    refine Finset.sum_congr rfl fun n hn ↦ ?_
    have hn₀ : (0 : ℝ) < n := by exact_mod_cast (Finset.mem_Icc.mp hn).1
    rw [Real.log_div (zero_lt_one.trans_le hY).ne' hn₀.ne']
  rw [heq]
  exact bound _ _ (Nat.floor_le (zero_le_one.trans hY)) (Nat.lt_floor_add_one Y).le

end RiemannMasullo.Selberg
