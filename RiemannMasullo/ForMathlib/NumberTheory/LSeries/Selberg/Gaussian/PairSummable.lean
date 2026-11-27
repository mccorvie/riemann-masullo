module

public import RiemannMasullo.ForMathlib.NumberTheory.LSeries.Selberg.Definitions
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

public section

open MeasureTheory Set

namespace RiemannMasullo.Selberg

private lemma freq_sq_lower {N k l : ℕ} (hk : k ∈ D N) (hl : l ∈ D N) (n : ℕ) :
    (n : ℝ) + 1 ≤ (freq n k l)^2 * (N : ℝ)^2 := by
  have hk₁ : (1 : ℝ) ≤ k := by exact_mod_cast (Finset.mem_Icc.mp hk).1
  have hl₀ : (0 : ℝ) < l := by exact_mod_cast (Finset.mem_Icc.mp hl).1
  have hlN : (l : ℝ) ≤ N := by exact_mod_cast (Finset.mem_Icc.mp hl).2
  have h : (n : ℝ) + 1 ≤ freq n k l * N := calc
    (n : ℝ) + 1 ≤ ((n : ℝ) + 1) * k := le_mul_of_one_le_right (by positivity) hk₁
    _ = freq n k l * l := by rw [freq, div_mul_cancel₀ _ hl₀.ne']
    _ ≤ freq n k l * N := mul_le_mul_of_nonneg_left hlN (by unfold freq; positivity)
  calc
    (n : ℝ) + 1 ≤ ((n : ℝ) + 1)^2 := le_self_pow₀ (by simp) two_ne_zero
    _ ≤ (freq n k l * N)^2 := pow_le_pow_left₀ (by positivity) h 2
    _ = _ := mul_pow _ _ _

/-- Keep Gaussian decay in the integration variable and geometric decay in each index. -/
private lemma exists_pair_majorant {N k l m v : ℕ} (hN : 2 ≤ N) (hk : k ∈ D N)
    (hl : l ∈ D N) (hm : m ∈ D N) (hv : v ∈ D N) {q : ℝ} (hq : 0 ≤ q) :
    ∃ c : ℝ, 0 < c ∧ ∀ (ij : ℕ × ℕ) (x : ℝ), 1 < x →
      x^(-q) * Real.exp (-Real.pi * Real.sin (1/(H N : ℝ)) *
        ((freq ij.1 k l)^2 + (freq ij.2 m v)^2) * x^2) ≤
      (Real.exp (ij.1 * -c) * Real.exp (ij.2 * -c)) * Real.exp (-c * x^2) := by
  have hN₀ : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hH : (1 : ℝ) ≤ H N := by
    exact_mod_cast (Nat.one_le_pow 100 N (by omega))
  let a := Real.pi * Real.sin (1/(H N : ℝ))
  have ha : 0 < a := by
    apply mul_pos Real.pi_pos (Real.sin_pos_of_pos_of_lt_pi ?_ ?_)
    · exact div_pos zero_lt_one (lt_of_lt_of_le zero_lt_one hH)
    · exact (div_le_one_of_le₀ hH (by positivity)).trans_lt (one_lt_two.trans_le Real.two_le_pi)
  let c := a / (N : ℝ)^2
  have hc : 0 < c := div_pos ha (sq_pos_of_pos hN₀)
  refine ⟨c, hc, fun ⟨i, j⟩ x hx ↦ ?_⟩
  have hfreq : (i : ℝ) + j + 1 ≤ ((freq i k l)^2 + (freq j m v)^2) * (N : ℝ)^2 := by
    linarith [freq_sq_lower hk hl i, freq_sq_lower hm hv j]
  have hx₂ : 1 ≤ x^2 := one_le_pow₀ hx.le
  have hij : (i : ℝ) + j ≤ ((i : ℝ) + j) * x^2 :=
    le_mul_of_one_le_right (by positivity) hx₂
  have hsplit : (i : ℝ) + j + x^2 ≤
      (((freq i k l)^2 + (freq j m v)^2) * (N : ℝ)^2) * x^2 := by
    linarith [mul_le_mul_of_nonneg_right hfreq (sq_nonneg x)]
  have hcancel : c * (N : ℝ)^2 = a := div_mul_cancel₀ _ (by positivity)
  apply le_trans (mul_le_of_le_one_left (Real.exp_pos _).le
    (Real.rpow_le_one_of_one_le_of_nonpos hx.le (neg_nonpos.mpr hq)))
  rw [← Real.exp_add, ← Real.exp_add, Real.exp_le_exp]
  rw [neg_mul]
  change -a * _ * x^2 ≤ (i : ℝ) * -c + (j : ℝ) * -c + -c * x^2
  rw [← hcancel]
  linarith [mul_le_mul_of_nonneg_left hsplit hc.le]

/-- Card 25, second part (added after the referee's check of the plan). Each absolute Gaussian
pair term is integrable on (1, ∞). The summability of the integrals in `pair_summable` does not
by itself allow the series to be exchanged with the integral, because the integral of a function
that is not integrable is zero in Lean; cards 26 and 28 use both statements.
Titchmarsh, §10.11, p. 270. -/
theorem pair_integrable (N k l m v : ℕ) (hN : 2 ≤ N) (hk : k ∈ D N) (hl : l ∈ D N)
    (hm : m ∈ D N) (hv : v ∈ D N) (q : ℝ) (hq : 0 ≤ q) (ij : ℕ × ℕ) :
    IntegrableOn (fun x : ℝ ↦ x^(-q)*Real.exp
      (-Real.pi*Real.sin (1/(H N : ℝ)) * ((freq ij.1 k l)^2+(freq ij.2 m v)^2)*x^2)) (Ioi 1) := by
  obtain ⟨c, hc, hbound⟩ := exists_pair_majorant hN hk hl hm hv hq
  apply Integrable.mono' (((integrable_exp_neg_mul_sq hc).const_mul
    (Real.exp (ij.1 * -c) * Real.exp (ij.2 * -c))).integrableOn)
  · fun_prop
  · filter_upwards [ae_restrict_mem (μ := volume) (measurableSet_Ioi (a := (1 : ℝ)))] with x hx
    have hx₀ : 0 ≤ x := le_trans zero_le_one hx.le
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact hbound ij x hx

/-- Card 25. For N ≥ 2, indices in [1,N], and q ≥ 0, the double series of integrals of the
absolute Gaussian pair terms converges.
Titchmarsh, §10.11, p. 270, absolute Fubini for the Gaussian double series. -/
theorem pair_summable (N k l m v : ℕ) (hN : 2 ≤ N) (hk : k ∈ D N) (hl : l ∈ D N)
    (hm : m ∈ D N) (hv : v ∈ D N) (q : ℝ) (hq : 0 ≤ q) :
    Summable (fun ij : ℕ × ℕ ↦ ∫ x in Ioi (1 : ℝ), x^(-q)*Real.exp
      (-Real.pi*Real.sin (1/(H N : ℝ)) * ((freq ij.1 k l)^2+(freq ij.2 m v)^2)*x^2)) := by
  obtain ⟨c, hc, hbound⟩ := exists_pair_majorant hN hk hl hm hv hq
  let w (n : ℕ) := Real.exp (n * -c)
  have hw : Summable w := Real.summable_exp_nat_mul_iff.mpr (neg_lt_zero.mpr hc)
  have hww := hw.mul_of_nonneg hw (fun n ↦ (Real.exp_pos _).le) (fun n ↦ (Real.exp_pos _).le)
  apply (hww.mul_right (∫ x in Ioi (1 : ℝ), Real.exp (-c * x^2))).of_nonneg_of_le
  · intro ij
    apply setIntegral_nonneg measurableSet_Ioi
    intro x hx
    have hx₀ : 0 ≤ x := le_trans zero_le_one hx.le
    positivity
  · intro ij
    rw [← integral_const_mul]
    exact setIntegral_mono_on (pair_integrable N k l m v hN hk hl hm hv q hq ij)
      (((integrable_exp_neg_mul_sq hc).const_mul (w ij.1 * w ij.2)).integrableOn)
      measurableSet_Ioi (hbound ij)

end RiemannMasullo.Selberg
