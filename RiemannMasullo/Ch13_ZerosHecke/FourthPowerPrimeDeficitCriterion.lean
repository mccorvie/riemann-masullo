module

public import RiemannMasullo.Ch13_ZerosHecke.HeckeRieszDeficitTransfer
public import RiemannMasullo.Ch13_ZerosHecke.HeckeRieszPerron

/-!
# The zero-free half-plane and cumulative fourth-power prime deficits

For each normalized Hecke character, a pointwise estimate for its genuine
centered ideal Riesz mean gives a cumulative estimate for its degree-one
prime deficits. The signed Landau implication gives the converse.
-/

public section

open Filter Function MeasureTheory NumberField Set
open scoped Asymptotics NNReal Classical

namespace RiemannMasullo

variable {K : Type*} [Field K] [NumberField K]
local notation "U" => PontryaginDual (IdeleClassGroup (𝓞 K) K)

/-- A zero-free half-plane gives both the all-cutoff inequality and its
asymptotic version for the genuine cumulative degree-one prime deficits. -/
theorem fourthPowerPrimeDeficit_bounds_of_no_right_zeros
    (τ : ℝ≥0ˣ →ₜ* IdeleClassGroup (𝓞 K) K) (hτ : RightInverse τ (ideleClassNorm K))
    (χ : U) (hχ : ∀ t, χ (τ t) = 1) {b : ℝ} (hb : 1 / 2 ≤ b) (hb' : b ≤ 1)
    (hz : ∀ p : ℂ, b < p.re → ¬ 0 < meromorphicOrderAt (continuedCompletedHeckeL χ) p)
    {ε : ℝ} (hε : 0 < ε) :
    (∃ M : ℝ, 0 ≤ M ∧ ∀ J : ℕ,
      ∑ j ∈ Finset.Icc 1 J, fourthPowerPrimeDeficit χ j ≤ M * (J : ℝ) ^ (4 * b + 5 + ε)) ∧
    (fun J : ℕ ↦ ∑ j ∈ Finset.Icc 1 J, fourthPowerPrimeDeficit χ j) =O[atTop]
      fun J ↦ (J : ℝ) ^ (4 * b + 5 + ε) := by
  obtain ⟨C, _, hC⟩ := heckeFirstRieszMean_bound_of_zeroFree_epsilon τ hτ χ hχ hb hb' hz
    (ε := ε / 4) (by positivity)
  rw [show 1 + b + ε / 4 = (b + ε / 4) + 1 by ring] at hC
  have hβ : 1 / 2 ≤ b + ε / 4 := by linarith
  simpa only [show 4 * (b + ε / 4) + 5 = 4 * b + 5 + ε by ring] using
    And.intro (fourthPowerPrimeDeficit_sum_le_of_centeredFirstRieszMean χ hβ hC)
      (fourthPowerPrimeDeficit_isBigO_of_centeredFirstRieszMean χ hβ hC)

/-- For a fixed normalized character, the cumulative fourth-power deficit has
every exponent strictly above `4b+5` exactly when its completed Hecke function
has no zero to the right of `b`. The endpoints `b = 1/2` and `b = 1` are included. -/
theorem hecke_no_right_zeros_iff_fourthPowerPrimeDeficit_growth
    (τ : ℝ≥0ˣ →ₜ* IdeleClassGroup (𝓞 K) K) (hτ : RightInverse τ (ideleClassNorm K))
    (χ : U) (hχ : ∀ t, χ (τ t) = 1) {b : ℝ} (hb : 1 / 2 ≤ b) (hb' : b ≤ 1) :
    (∀ p : ℂ, b < p.re → ¬ 0 < meromorphicOrderAt (continuedCompletedHeckeL χ) p) ↔
    ∀ ε : ℝ, 0 < ε →
      (fun J : ℕ ↦ ∑ j ∈ Finset.Icc 1 J, fourthPowerPrimeDeficit χ j) =O[atTop]
        fun J ↦ (J : ℝ) ^ (4 * b + 5 + ε) :=
  ⟨fun hz _ hε ↦ (fourthPowerPrimeDeficit_bounds_of_no_right_zeros τ hτ χ hχ hb hb' hz hε).2,
    hecke_no_right_zeros_of_fourthPowerPrimeDeficit_growth τ hτ χ hχ hb hb'⟩

end RiemannMasullo
