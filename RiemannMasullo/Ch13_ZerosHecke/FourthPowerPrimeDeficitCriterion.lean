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

attribute [local instance] instIdeleClassMeasurableSpaceSec1 instIdeleClassBorelSpaceSec1
  instIdeleClassT2Sec1 instIdeleClassLocallyCompactSec1 instIdeleClassSecondCountableSec1

local notation "ord(" χ ", " p ")" =>
  MeromorphicOn.divisor (continuedCompletedHeckeL (F := K) χ) univ p

/-- Paper: Theorem 12.5.1.1, pp. 519–520. The exterior trace statement at all
positive widths is equivalent to the cumulative degree-one prime deficit bound
with exponent `7+ε` for every normalized character of this field. -/
theorem hasSum_exteriorZeros_iff_fourthPowerPrimeDeficit_growth
    (τ : ℝ≥0ˣ →ₜ* IdeleClassGroup (𝓞 K) K) (hτ : RightInverse τ (ideleClassNorm K)) :
    (∀ a : ℝ, 0 < a → ∀ φ : BruhatCompactSupport (IdeleClassGroup (𝓞 K) K),
      (∀ g : (ideleClassNorm K).ker, φ.val g = 0) →
      HasSum (fun z : {p : {χ : U // ∀ t : ℝ≥0ˣ, χ (τ t) = 1} × ℂ //
          0 < ord(p.1.val, p.2) ∧ a ≤ |p.2.re - 1 / 2|} ↦ (ord(z.val.1.val, z.val.2) : ℂ) *
        ∫ g, φ.val g * ideleClassNormTwist z.val.1.val (z.val.2 - 1 / 2) g
          ∂ideleClassTamagawaMeasure K) 0) ↔
    ∀ χ : U, (∀ t, χ (τ t) = 1) → ∀ ε : ℝ, 0 < ε →
      (fun J : ℕ ↦ ∑ j ∈ Finset.Icc 1 J, fourthPowerPrimeDeficit χ j) =O[atTop]
        fun J ↦ (J : ℝ) ^ (7 + ε) := by
  refine ⟨?_, hasSum_exteriorZeros_of_fourthPowerPrimeDeficit_growth τ hτ⟩
  intro h χ hχ ε hε
  have he := (hasSum_exteriorZeros_iff_centeredRealRieszLogDeriv τ hτ).mp h χ hχ
  have hz := (hecke_centeredRealRieszLogDeriv_continuation_iff τ hτ χ hχ (a := 0)
    le_rfl (by norm_num)).mp (by simpa only [zero_add] using he)
  simp only [zero_add] at hz
  have hbound := (fourthPowerPrimeDeficit_bounds_of_no_right_zeros τ hτ χ hχ
    (b := 1/2) le_rfl (by norm_num) hz hε).2
  norm_num at hbound
  exact hbound

end RiemannMasullo
