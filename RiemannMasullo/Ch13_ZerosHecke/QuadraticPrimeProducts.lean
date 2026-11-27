module

public import RiemannMasullo.Ch13_ZerosHecke.QuadraticPrimeCellMoments
import Mathlib.Data.Nat.Choose.Bounds

/-! # Products of distinct dyadic auxiliary primes -/

@[expose] public noncomputable section

open Finset Filter

namespace RiemannMasullo

private theorem auxPrime_pow_le_choose {n h : ℕ} (hn : 2*h ≤ n) :
    (n:ℝ)^h ≤ (2:ℝ)^h * h.factorial * n.choose h := by
  have hc := (div_le_iff₀ (show (0:ℝ) < h.factorial by exact_mod_cast h.factorial_pos)).mp
    (Nat.pow_le_choose (α := ℝ) h n)
  have hs : (n:ℝ) ≤ 2*((n+1-h:ℕ):ℝ) := by exact_mod_cast (show n ≤ 2*(n+1-h) by omega)
  calc _ ≤ (2*((n+1-h:ℕ):ℝ))^h := pow_le_pow_left₀ (Nat.cast_nonneg _) hs _
       _ = (2:ℝ)^h * (((n+1-h:ℕ):ℝ))^h := mul_pow ..
       _ ≤ (2:ℝ)^h * ((n.choose h:ℝ)*h.factorial) :=
         mul_le_mul_of_nonneg_left hc (by positivity)
       _ = _ := by ring

/-- There are sufficiently many unordered products of `h` distinct dyadic auxiliary primes.
The count is the binomial coefficient of the actual number of primes in the interval. -/
theorem quadraticPrime_fourthPower_distinctProduct_count (h : ℕ) :
    ∀ᶠ J : ℕ in atTop, let U := Nat.primesLE (2*J^12) \ Nat.primesLE (J^12)
      h ≤ U.card ∧ ((J:ℝ)^12)^h ≤
        ((4:ℝ)^h*h.factorial)*(U.powersetCard h).card * (Real.log (2*(J:ℝ)^12))^h := by
  filter_upwards [quadraticPrime_fourthPower_auxiliary_data, eventually_ge_atTop (52*h)] with J hg hJh
  intro U
  obtain ⟨hJ, _, _, _, _, hc⟩ := hg
  have hj : 0 < (J:ℝ) := by exact_mod_cast (show 0 < J by omega)
  have hj1 : 1 ≤ (J:ℝ) := by linarith [(show (2:ℝ) ≤ J by exact_mod_cast hJ)]
  have hlog : Real.log (2*(J:ℝ)^12) ≤ 13*J := by
    rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow]
    have h2 := Real.log_le_sub_one_of_pos (by norm_num : 0 < (2:ℝ))
    have hx := Real.log_le_sub_one_of_pos hj
    norm_num
    linarith
  have hlog0 : 0 ≤ Real.log (2*(J:ℝ)^12) := Real.log_nonneg
    (one_le_mul_of_one_le_of_one_le (by norm_num) (one_le_pow₀ hj1))
  have hcount : (J:ℝ) ≤ 26*U.card := by
    apply le_of_mul_le_mul_right _ hj
    calc (J:ℝ)*J = (J:ℝ)^2 := (pow_two _).symm
         _ ≤ (J:ℝ)^12 := pow_le_pow_right₀ hj1 (by decide)
         _ ≤ _ := hc
         _ ≤ 2*(U.card:ℝ)*(13*J) := mul_le_mul_of_nonneg_left hlog (by positivity)
         _ = _ := by ring
  have hh : 2*h ≤ U.card := by
    have h' : J ≤ 26*U.card := by exact_mod_cast hcount
    omega
  refine ⟨by omega, ?_⟩
  rw [card_powersetCard]
  calc _ ≤ (2*(U.card:ℝ)*Real.log (2*(J:ℝ)^12))^h := pow_le_pow_left₀ (by positivity) hc h
       _ = ((2:ℝ)^h * (U.card:ℝ)^h)*(Real.log (2*(J:ℝ)^12))^h := by rw [mul_pow, mul_pow]
       _ ≤ ((2:ℝ)^h * ((2:ℝ)^h*h.factorial*U.card.choose h))*(Real.log (2*(J:ℝ)^12))^h := by
         exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
           (auxPrime_pow_le_choose hh) (by positivity)) (pow_nonneg hlog0 _)
       _ = _ := by rw [show (4:ℝ)^h = 2^h*2^h by rw [← mul_pow]; norm_num]; ring

end RiemannMasullo
