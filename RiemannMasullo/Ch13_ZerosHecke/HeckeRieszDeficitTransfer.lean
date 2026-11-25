module

public import RiemannMasullo.Ch13_ZerosHecke.FourthPowerRieszSampling
public import RiemannMasullo.Ch13_ZerosHecke.HeckePrimeLowerBound

/-! # Uniform centered first Riesz estimates at fourth powers

This consumer uses the degree-one comparison from PR #7587 and the actual fourth-power
deficit from the integrated `HeckePrimeLowerBound` module. -/

public section

open NumberField Filter
open scoped Classical

namespace RiemannMasullo

variable {K : Type*} [Field K] [NumberField K]

/-- At every integer cutoff the cumulative degree-one prime deficit costs at most a fixed
constant times `J^(4*b+5)` under a uniform bound for the centered full first Riesz mean. -/
theorem fourthPowerPrimeDeficit_sum_le_of_centeredFirstRieszMean
    (χ : PontryaginDual (IdeleClassGroup (𝓞 K) K)) {b C : ℝ} (hb : 1 / 2 ≤ b)
    (hfull : ∀ x : ℝ, 1 ≤ x →
      |(heckeFirstRieszMean χ x).re - (if χ = 1 then 1 else 0) * x ^ 2 / 2| ≤ C * x ^ (b + 1)) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ J : ℕ,
      ∑ j ∈ Finset.Icc 1 J, fourthPowerPrimeDeficit χ j ≤ M * (J : ℝ) ^ (4 * b + 5) := by
  obtain ⟨E, hE⟩ := heckeFirstRieszMean_sub_prime_le
  let D := (Module.finrank ℚ K : ℝ)
  have hD : 0 ≤ D := Nat.cast_nonneg _
  have hC : 0 ≤ C := by simpa using (abs_nonneg _).trans (hfull 1 le_rfl)
  have hprime (x : ℝ) (hx : 1 ≤ x) :
      (heckeFirstRieszMean χ x).re - degreeOnePrimeFirstRieszMean χ x ≤
        (D * |E|) * (x * Real.sqrt x) := by
    have hx₀ : 0 ≤ x := zero_le_one.trans hx
    have hrem := (Complex.abs_re_le_norm _).trans (hE K χ hx₀)
    simp only [Complex.sub_re, Complex.re_sum, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      mul_zero, sub_zero] at hrem
    change |(heckeFirstRieszMean χ x).re - degreeOnePrimeFirstRieszMean χ x| ≤
      D * x * (E * Real.sqrt x) at hrem
    calc
      (heckeFirstRieszMean χ x).re - degreeOnePrimeFirstRieszMean χ x ≤
          D * x * (E * Real.sqrt x) := (le_abs_self _).trans hrem
      _ ≤ D * x * (|E| * Real.sqrt x) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (le_abs_self E) (Real.sqrt_nonneg x))
          (mul_nonneg hD hx₀)
      _ = (D * |E|) * (x * Real.sqrt x) := by ring
  have hDE : 0 ≤ D * |E| := mul_nonneg hD (abs_nonneg _)
  let mainTerm (x : ℝ) := (if χ = 1 then 1 else 0 : ℝ) * x ^ 2 / 2
  refine ⟨C + D * |E|, add_nonneg hC hDE, fun J ↦ ?_⟩
  apply sum_fourthPower_negPart_le_of_pointwise (fun x ↦ (heckeFirstRieszMean χ x).re - mainTerm x)
    (fun x ↦ degreeOnePrimeFirstRieszMean χ x - mainTerm x) hb hC hDE
  · intro x hx
    exact (neg_le_abs _).trans (hfull x hx)
  · intro x hx
    linarith only [hprime x hx]

/-- The cumulative genuine prime deficits satisfy the exact endpoint Big-O bound. -/
theorem fourthPowerPrimeDeficit_isBigO_of_centeredFirstRieszMean
    (χ : PontryaginDual (IdeleClassGroup (𝓞 K) K)) {b C : ℝ} (hb : 1 / 2 ≤ b)
    (hfull : ∀ x : ℝ, 1 ≤ x →
      |(heckeFirstRieszMean χ x).re - (if χ = 1 then 1 else 0) * x ^ 2 / 2| ≤ C * x ^ (b + 1)) :
    (fun J : ℕ ↦ ∑ j ∈ Finset.Icc 1 J, fourthPowerPrimeDeficit χ j) =O[atTop]
      fun J ↦ (J : ℝ) ^ (4 * b + 5) := by
  obtain ⟨M, _, hM⟩ := fourthPowerPrimeDeficit_sum_le_of_centeredFirstRieszMean χ hb hfull
  apply Asymptotics.IsBigO.of_bound M
  filter_upwards with J
  rw [Real.norm_of_nonneg (Finset.sum_nonneg (fun j _ ↦
    show 0 ≤ fourthPowerPrimeDeficit χ j from le_max_right _ _)),
    Real.norm_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg J) _)]
  exact hM J

end RiemannMasullo
