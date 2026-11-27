module

public import RiemannMasullo.ForMathlib.NumberTheory.LSeries.Selberg.Definitions
import RiemannMasullo.ForMathlib.NumberTheory.LSeries.Selberg.Arithmetic.EnergyRows
import RiemannMasullo.ForMathlib.NumberTheory.LSeries.Selberg.Arithmetic.JordanSum
import RiemannMasullo.ForMathlib.NumberTheory.LSeries.Selberg.Gaussian.ThetaMellinError

public section

open MeasureTheory Set

namespace RiemannMasullo.Selberg

private lemma scale_pos {N : ℕ} (hN : 2 ≤ N) : 0 < scale N := by
  have hH : (1 : ℝ) ≤ H N := by exact_mod_cast Nat.one_le_pow 100 N (by omega)
  have hsin : 0 < Real.sin (1 / (H N : ℝ)) :=
    Real.sin_pos_of_pos_of_lt_pi (div_pos zero_lt_one (zero_lt_one.trans_le hH))
      ((div_le_one_of_le₀ hH (by positivity)).trans_lt (one_lt_two.trans_le Real.two_le_pi))
  exact Real.sqrt_pos.2 (mul_pos (mul_pos zero_lt_two Real.pi_pos) hsin)

private lemma abs_coef_le_one {N : ℕ} {b : ℕ → ℝ} (hb : bd N b) {k l m v : ℕ}
    (hk : k ∈ D N) (hl : l ∈ D N) (hm : m ∈ D N) (hv : v ∈ D N) :
    |coef b k l m v| ≤ 1 := by
  have hl₁ : (1 : ℝ) ≤ l := by exact_mod_cast (Finset.mem_Icc.mp hl).1
  have hv₁ : (1 : ℝ) ≤ v := by exact_mod_cast (Finset.mem_Icc.mp hv).1
  have hden := one_le_mul_of_one_le_of_one_le hl₁ hv₁
  simp only [coef, abs_div, abs_mul, Nat.abs_cast]
  apply div_le_one_of_le₀ _ (by positivity)
  calc
    |b k| * |b l| * |b m| * |b v| ≤ 1 * 1 * 1 * 1 := by
      gcongr <;> apply hb <;> assumption
    _ ≤ _ := by simpa using hden

/-- Apply the Mellin estimate at scale `s / r`, retaining both signed main terms. -/
private lemma weighted_theta_upper {q s r c : ℝ} (hq : 0 < q) (hq' : q ≤ 1 / 2)
    (hs : 0 < s) (hr : 0 < r) (hc : |c| ≤ 1) :
    c * (∫ x in Ioi (1 : ℝ), x ^ (-q) * theta (s / r * x)) ≤
      gaussC / (q * s) * (c * r) + (s ^ (q - 1) * errorC q) * (c * r ^ (1 - q)) + 2 := by
  have herr := (theta_mellin_error q (s / r) hq hq' (div_pos hs hr)).2
  have hpow : (s / r) ^ (q - 1) = s ^ (q - 1) * r ^ (1 - q) := by
    rw [Real.div_rpow hs.le hr.le, div_eq_mul_inv, ← Real.rpow_neg hr.le, neg_sub]
  have hmain : gaussC / (q * (s / r)) = gaussC / (q * s) * r := by
    field_simp
  rw [hmain, hpow] at herr
  have hweighted := mul_le_mul hc herr (abs_nonneg _) zero_le_one
  rw [← abs_mul, one_mul] at hweighted
  linarith only [(le_abs_self _).trans hweighted]

/-- Card 29. For bounded coefficients and 0 < q ≤ 1/2, the diagonal is at most `gaussC * energy N
b 1 / (q * scale N) + 2 N⁴`.
One-sided version of Titchmarsh (10.11.1), (10.15.1), pp. 271, 274. -/
theorem diagonal_upper (N : ℕ) (hN : 2 ≤ N) (b : ℕ → ℝ) (hb : bd N b)
    (q : ℝ) (hq : 0 < q) (hq' : q ≤ 1/2) :
    diag N b q ≤ gaussC * energy N b 1 / (q * scale N) + 2*(N : ℝ)^4 := by
  have hs := scale_pos hN
  let A := gaussC / (q * scale N)
  let B := scale N ^ (q - 1) * errorC q
  have hB : B ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (Real.rpow_nonneg hs.le _)
    (theta_mellin_error q 1 hq hq' zero_lt_one).1
  have hp : 0 < 1 - q := by linarith
  have henergy : 0 ≤ energy N b (1 - q) := by
    rw [energy_rows N b (1 - q) hp]
    exact Finset.sum_nonneg fun r hr ↦
      mul_nonneg (jordan_sum _ hp r (Finset.mem_Icc.mp hr).1).2.1 (sq_nonneg _)
  calc
    diag N b q ≤ fourSum N (fun k l m v ↦
        A * (coef b k l m v * ratio k l m v ^ (1 : ℝ)) +
        B * (coef b k l m v * ratio k l m v ^ (1 - q)) + 2) := by
      unfold diag fourSum
      refine Finset.sum_le_sum fun k hk ↦ Finset.sum_le_sum fun l hl ↦
        Finset.sum_le_sum fun m hm ↦ Finset.sum_le_sum fun v hv ↦ ?_
      have hk₀ : 0 < k := (Finset.mem_Icc.mp hk).1
      have hm₀ : 0 < m := (Finset.mem_Icc.mp hm).1
      have hv₀ : 0 < v := (Finset.mem_Icc.mp hv).1
      have hr : 0 < ratio k l m v := by
        unfold ratio
        apply div_pos _ (by positivity)
        exact_mod_cast Nat.gcd_pos_of_pos_left (l * m) (Nat.mul_pos hk₀ hv₀)
      simp only [Real.rpow_one]
      exact weighted_theta_upper hq hq' hs hr (abs_coef_le_one hb hk hl hm hv)
    _ = A * energy N b 1 + B * energy N b (1 - q) + 2 * (N : ℝ)^4 := by
      simp only [energy, fourSum, Finset.sum_add_distrib, Finset.mul_sum]
      simp [D, Finset.sum_const, nsmul_eq_mul]
      ring
    _ ≤ _ := by
      rw [div_mul_eq_mul_div₀ gaussC (energy N b 1) (q * scale N)]
      exact add_le_add_left (add_le_of_nonpos_right
        (mul_nonpos_of_nonpos_of_nonneg hB henergy)) _

end RiemannMasullo.Selberg
