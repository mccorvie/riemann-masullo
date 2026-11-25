module

public import RiemannMasullo.Ch12_TraceGeometric.Sec4_WeightedBandAverageLimit
public import RiemannMasullo.Ch12_TraceGeometric.Sec4_RealPWLevelPrincipalValue

/-! # The level of the weighted model against the principal value of the project

Paper: Theorem 12.4.1.1, pp. 514–519, with Definition B.4.4.1(2), p. 620, and p. 520.

`Sec4_WeightedBandAverageLimit` gives the limit of the traces on the level of the weighted
model against a test function as an explicit integral. This file writes that limit with the
principal value of the project at the real place of `ℚ`.

* `tendsto_hilbertTrace_weightedLevel_principalValue_sub`: for an even test `f` at the real
  place supported in `±[a, b]` with `1 < a`, with profile `φ`, the Hilbert traces of
  `P ∘ M_L ∘ A ∘ P` on the level of the weighted model tend to
  `infiniteConnesWeilPrincipalValue` of `f` minus `∫ φ (g) (g ^ (1/2) + g ^ (-1/2)) dg / g`.
  The two integrals subtracted are the two pole terms that p. 520 subtracts.

In the unweighted model the limit is the principal value minus
`∫ φ (g) min (g ^ (1/2), g ^ (-1/2)) dg / g`
(`ratEmpty_tendsto_hilbertTrace_principalValue_sub`): one pole term for each `g`.

**Not formalized.** No test is constructed here: the statement holds for every test of the
project with the stated profile. The test is supported in dilations larger than one. One
weight, `x ^ 2 + x ^ (-2)`, the sharp cutoff, and the rational field with no finite place.
-/

@[expose] public noncomputable section

open Filter Function IsDedekindDomain MeasureTheory NumberField Set
open scoped NNReal ENNReal NumberField.AdeleRing Topology InnerProductSpace

namespace RiemannMasullo

set_option quotPrecheck false
set_option maxSynthPendingDepth 8

attribute [local instance] instInfiniteCompletionMeasurableSec4b

local notation "K∞" => (Rat.infinitePlace).Completion
local notation "r∞" => InfinitePlace.Completion.ringEquivRealOfIsReal Rat.isReal_infinitePlace
local notation "Hw" => Lp ℂ 2 weightedBandMeasure

/-- For `g > 1` the real-place term `(1/2) (√g / |1 - g| + √g / |1 + g|)` is
`g ^ (3/2) / (g ^ 2 - 1)`. -/
theorem half_sqrt_div_abs_add_eq {g : ℝ} (hg : 1 < g) :
    1 / 2 * (√g / |1 - g| + √g / |1 + g|) = g ^ (3 / 2 : ℝ) / (g ^ 2 - 1) := by
  have hg0 : 0 < g := by linarith
  have h32 : g ^ (3 / 2 : ℝ) = g * √g := by
    rw [Real.sqrt_eq_rpow, show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add hg0,
      Real.rpow_one]
  have h1 : g - 1 ≠ 0 := by linarith
  have h2 : 1 + g ≠ 0 := by linarith
  have h3 : g ^ 2 - 1 ≠ 0 := by nlinarith
  rw [abs_of_neg (by linarith : 1 - g < 0), neg_sub, abs_of_pos (by linarith : 0 < 1 + g), h32]
  field_simp
  ring

/-- Paper: Theorem 12.4.1.1, pp. 514–519, with Definition B.4.4.1(2), p. 620, and p. 520.
**On the level of the weighted model the traces tend to the principal value of the project
minus both pole terms.** Over `ℚ` with no finite place, at order zero, with the weight
`x ^ 2 + x ^ (-2)`: let `f` be a test at the real place that is even and supported in
`±[a, b]`, with `1 < a` and profile `φ`. The Hilbert traces of `P ∘ M_L ∘ A ∘ P` on the level
`weightedLevel Y` tend, as `L → ∞` at fixed `Y > 0`, to `infiniteConnesWeilPrincipalValue` of
`f` minus `∫ φ (g) (g ^ (1/2) + g ^ (-1/2)) dg / g`.
Reconstruction: as for `tendsto_hilbertTrace_weightedLevel_average_compression`. For `F = ℚ`
and `S = ∅` the sum `principalValues` of `sLocalTrace_asymptotic_of_sharp_comparison` is this
one principal value. -/
theorem tendsto_hilbertTrace_weightedLevel_principalValue_sub {Y a b : ℝ} {φ : ℝ → ℝ}
    (hY : 0 < Y) (ha : 1 < a) (hab : a ≤ b) (hφ : ContinuousOn φ (Icc a b))
    (f : BruhatCompactSupport K∞ˣ)
    (hf : ∀ u : K∞ˣ, f.val u = if |r∞ u.val| ∈ Icc a b then (φ |r∞ u.val| : ℂ) else 0) :
    ∃ tr : ℝ → ℂ,
      (∀ L : ℝ, 0 ≤ L → ∃ hn : IsNuclearOperator ((weightedLevel Y).starProjection ∘L
          (weightedBandCutoff L ∘L weightedBandDilationAverage φ a b) ∘L
          (weightedLevel Y).starProjection), hilbertTrace ⟨_, hn⟩ = tr L) ∧
      Tendsto tr atTop (𝓝 (infiniteConnesWeilPrincipalValue Rat.infinitePlace f -
        ((∫ g in a..b, φ g * (√g + (√g)⁻¹) / g : ℝ) : ℂ))) := by
  obtain ⟨tr, htr, hlim⟩ := tendsto_hilbertTrace_weightedLevel_average_compression hY ha hab hφ
  refine ⟨tr, htr, ?_⟩
  have h1 : (1 : ℝ) ∉ Icc a b := fun h ↦ absurd h.1 (not_le.mpr ha)
  have hsub : Icc a b ⊆ Ioi 1 := fun g hg ↦ ha.trans_le hg.1
  have hpos : ∀ g ∈ Icc a b, g ≠ 0 := fun g hg ↦ (zero_lt_one.trans (hsub hg)).ne'
  have hsq : ∀ g ∈ Icc a b, √g ≠ 0 := fun g hg ↦
    (Real.sqrt_pos.mpr (zero_lt_one.trans (hsub hg))).ne'
  have hV : ContinuousOn (fun g : ℝ ↦ g ^ (3 / 2 : ℝ) / (g ^ 2 - 1)) (Icc a b) :=
    ContinuousOn.div (Real.continuous_rpow_const (by norm_num)).continuousOn (by fun_prop)
      fun g hg ↦ by
        have : (1 : ℝ) < g := hsub hg
        nlinarith
  have i1 : IntervalIntegrable (fun g : ℝ ↦ φ g * (g ^ (3 / 2 : ℝ) / (g ^ 2 - 1)) / g)
      volume a b :=
    ContinuousOn.intervalIntegrable_of_Icc hab ((hφ.mul hV).div continuousOn_id hpos)
  have i2 : IntervalIntegrable (fun g : ℝ ↦ φ g * (√g + (√g)⁻¹) / g) volume a b :=
    ContinuousOn.intervalIntegrable_of_Icc hab ((hφ.mul
      (Real.continuous_sqrt.continuousOn.add
        (ContinuousOn.inv₀ Real.continuous_sqrt.continuousOn hsq))).div continuousOn_id hpos)
  have hpv : ∫ g in a..b, φ g * (1 / 2 * (√g / |1 - g| + √g / |1 + g|)) / g =
      ∫ g in a..b, φ g * (g ^ (3 / 2 : ℝ) / (g ^ 2 - 1)) / g := by
    refine intervalIntegral.integral_congr fun g hg ↦ ?_
    rw [uIcc_of_le hab] at hg
    simp only [half_sqrt_div_abs_add_eq (hsub hg)]
  have heq : (∫ g in a..b, φ g * (g ^ (3 / 2 : ℝ) / (g ^ 2 - 1)) / g) -
      ∫ g in a..b, φ g * (√g + (√g)⁻¹) / g =
      ∫ g in a..b, φ g * (g ^ (3 / 2 : ℝ) / (g ^ 2 - 1) - (√g)⁻¹ - √g) / g := by
    rw [← intervalIntegral.integral_sub i1 i2]
    refine intervalIntegral.integral_congr fun g _ ↦ ?_
    ring
  rw [ratInfiniteConnesWeilPrincipalValue_eq (by linarith) hab h1 hφ f hf, ← Complex.ofReal_sub,
    hpv, heq]
  exact hlim

end RiemannMasullo
