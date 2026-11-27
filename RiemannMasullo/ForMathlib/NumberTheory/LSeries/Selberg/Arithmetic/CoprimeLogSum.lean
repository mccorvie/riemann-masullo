module

public import RiemannMasullo.ForMathlib.NumberTheory.LSeries.Selberg.Definitions
import Mathlib.Algebra.Order.Floor.Semifield
import RiemannMasullo.ForMathlib.NumberTheory.LSeries.Selberg.Arithmetic.RemovePrimes
import RiemannMasullo.ForMathlib.NumberTheory.LSeries.Selberg.Arithmetic.SmoothMassBound
import RiemannMasullo.ForMathlib.NumberTheory.LSeries.Selberg.Arithmetic.UntwistedLogSum

public section

open Classical

namespace RiemannMasullo.Selberg

/-- Parametrize the positive multiples of `d` through `N` by their quotients. -/
private theorem sum_multiples (N d : ℕ) (hd : 0 < d) (f : ℕ → ℝ) :
    ∑ n ∈ (D N).filter (d ∣ ·), f n = ∑ k ∈ D (N / d), f (k * d) := by
  symm
  apply Finset.sum_nbij' (· * d) (· / d)
  · intro k hk
    obtain ⟨hk₁, hk₂⟩ := Finset.mem_Icc.mp hk
    exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr
      ⟨Nat.mul_pos hk₁ hd, (Nat.le_div_iff_mul_le hd).mp hk₂⟩, dvd_mul_left _ _⟩
  · intro n hn
    obtain ⟨hnN, hdvd⟩ := Finset.mem_filter.mp hn
    obtain ⟨hn₁, hn₂⟩ := Finset.mem_Icc.mp hnN
    exact Finset.mem_Icc.mpr ⟨Nat.div_pos (Nat.le_of_dvd hn₁ hdvd) hd,
      Nat.div_le_div_right hn₂⟩
  · exact fun k _ ↦ Nat.mul_div_cancel k hd
  · exact fun n hn ↦ Nat.div_mul_cancel (Finset.mem_filter.mp hn).2
  · exact fun _ _ ↦ rfl

/-- Removing the primes of `r` expresses the restricted sum as a finite sum of untwisted ones. -/
private theorem logSum_eq_sum_untwisted (r : ℕ) (Y : ℝ) (hr : 0 < r) :
    logSum r Y = ∑ d ∈ (D ⌊Y⌋₊).filter (smooth r),
      posHalf d / d * logSum 1 (Y / d) := by
  classical
  let N := ⌊Y⌋₊
  let w (n d : ℕ) := posHalf d * alpha (n / d) / n * Real.log (Y / n)
  calc
    logSum r Y = ∑ n ∈ D N, ∑ d ∈ n.divisors.filter (smooth r), w n d := by
      rw [logSum, Finset.sum_filter]
      refine Finset.sum_congr rfl fun n hn ↦ ?_
      have h := remove_primes r n hr (Finset.mem_Icc.mp hn).1
      simpa only [w, ite_div, ite_mul, zero_div, zero_mul, Finset.sum_div, Finset.sum_mul]
        using congrArg (fun a : ℝ ↦ a / n * Real.log (Y / n)) h
    _ = ∑ d ∈ (D N).filter (smooth r), ∑ n ∈ (D N).filter (d ∣ ·), w n d := by
      apply Finset.sum_comm'
      intro n d
      simp only [Finset.mem_filter, Nat.mem_divisors]
      constructor
      · rintro ⟨hn, ⟨hdvd, hn₀⟩, hs⟩
        exact ⟨⟨hn, hdvd⟩, Finset.mem_Icc.mpr ⟨Nat.pos_of_dvd_of_pos hdvd hn₀.bot_lt,
          (Nat.le_of_dvd hn₀.bot_lt hdvd).trans (Finset.mem_Icc.mp hn).2⟩, hs⟩
      · rintro ⟨⟨hn, hdvd⟩, _, hs⟩
        have hn₀ : 0 < n := (Finset.mem_Icc.mp hn).1
        exact ⟨hn, ⟨hdvd, hn₀.ne'⟩, hs⟩
    _ = _ := by
      refine Finset.sum_congr rfl fun d hd ↦ ?_
      have hd₀ : 0 < d := (Finset.mem_Icc.mp (Finset.mem_filter.mp hd).1).1
      rw [sum_multiples N d hd₀, logSum, Nat.floor_div_natCast,
        Finset.filter_true_of_mem (fun k _ ↦ Nat.coprime_one_left k), Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ ↦ ?_
      simp only [w, Nat.mul_div_cancel _ hd₀, Nat.cast_mul, mul_comm (k : ℝ) d,
        div_eq_mul_inv, mul_inv_rev]
      ac_rfl

/-- Card 6. Restricting the logarithmic sum through Y to indices coprime to r gives an absolute
bound of order `smoothMass r * √(1 + log Y)`, uniformly in r and Y.
Replacement for Titchmarsh Lemma 10.12, (10.12.1), pp. 271–272. -/
theorem coprime_logSum : ∃ C > (0 : ℝ), ∀ (r : ℕ) (Y : ℝ), 0 < r → 1 ≤ Y →
    |logSum r Y| ≤ C * smoothMass r * Real.sqrt (1 + Real.log Y) := by
  obtain ⟨C, hC, hsum⟩ := untwisted_logSum
  refine ⟨C, hC, ?_⟩
  intro r Y hr hY
  let S := (D ⌊Y⌋₊).filter (smooth r)
  let B := C * Real.sqrt (1 + Real.log Y)
  have hB : 0 ≤ B := mul_nonneg hC.le (Real.sqrt_nonneg _)
  rw [logSum_eq_sum_untwisted r Y hr]
  calc
    _ ≤ ∑ d ∈ S, |posHalf d / d * logSum 1 (Y / d)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ d ∈ S, (d : ℝ)⁻¹ * B := by
      refine Finset.sum_le_sum fun d hd ↦ ?_
      obtain ⟨hd₁, hd₂⟩ := Finset.mem_Icc.mp (Finset.mem_filter.mp hd).1
      have hdR : 1 ≤ (d : ℝ) := by exact_mod_cast hd₁
      have hdpos := zero_lt_one.trans_le hdR
      have hlow : 1 ≤ Y / d := (one_le_div hdpos).mpr
        ((Nat.cast_le.mpr hd₂).trans (Nat.floor_le (zero_le_one.trans hY)))
      have hhigh := div_le_self (zero_le_one.trans hY) hdR
      have hlog := Real.log_le_log (zero_lt_one.trans_le hlow) hhigh
      have hbound : |logSum 1 (Y / d)| ≤ B := (hsum _ hlow).trans
        (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (add_le_add_right hlog 1)) hC.le)
      have hpos : 0 ≤ posHalf d := (abs_nonneg _).trans (spectralLineJet_selbergHalfZeta_spec.1 d)
      rw [abs_mul, abs_of_nonneg (div_nonneg hpos hdpos.le)]
      apply mul_le_mul _ hbound (abs_nonneg _) (inv_nonneg.mpr hdpos.le)
      rw [← one_div]
      exact div_le_div_of_nonneg_right (show posHalf d ≤ 1 from spectralLineJet_selberg_half_le_one d)
        hdpos.le
    _ = (∑ d ∈ S, (d : ℝ)⁻¹) * B := (Finset.sum_mul ..).symm
    _ ≤ smoothMass r * B := mul_le_mul_of_nonneg_right (smooth_mass_bound r _ hr) hB
    _ = _ := by dsimp [B]; ring

end RiemannMasullo.Selberg
