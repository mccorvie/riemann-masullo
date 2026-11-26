module

public import RiemannMasullo.AppB_AnalyticNT.Sec4b
public import RiemannMasullo.Ch12_TraceGeometric.Sec4_RealPWLevelTransport
import RiemannMasullo.ForMathlib.MeasureTheory.Group.Arithmetic
import Mathlib.Topology.Algebra.IsOpenUnits

/-! # The limit of the traces against the principal value of the project, over `ℚ`

Paper: Theorem 12.4.1.1, pp. 514–519, with Definition B.4.4.1(2), p. 620.

`Sec4_RealPWLevelTransport` gives the limit of the traces of the compression on the level of the
project as two explicit integrals. This file identifies the first with the principal value that
the project's statement of the theorem uses, `infiniteConnesWeilPrincipalValue` at the real
place, so that the conclusion can be compared with `sLocalTrace_asymptotic_of_sharp_comparison`.
For `F = ℚ` and `S = ∅` the sum `principalValues` of that statement has this one term.

* `integral_ratInfiniteMultiplicative`: the multiplicative measure of the project at the real
  place of `ℚ` is `dx / |x|` in the real coordinate.
* `ratInfiniteConnesWeilPrincipalValue_eq`: for an even test at the real place supported in
  `±[a, b]`, with profile `φ` and `1` outside `[a, b]`, the principal value is
  `∫ φ(g) (1/2) (√g / |1 - g| + √g / |1 + g|) dg / g`. This uses
  `realConnesWeilPrincipalValue_of_apply_one_zero`.
* `ratEmpty_tendsto_hilbertTrace_principalValue_sub`: the Hilbert traces of
  `P_Y ∘ χ_L ∘ A ∘ P_Y` on the level of the project tend, as `Y * L → ∞`, to the principal value
  of the test minus `∫ φ(g) min(g^(1/2), g^(-1/2)) d×g`.
* `ratEmpty_not_tendsto_hilbertTrace_principalValue`: when that integral is not zero, the traces
  do not tend to the principal value. By `integral_mul_min_sqrt_pos` the integral is positive
  when `φ` is positive on `(a, b)`.

**Not formalized.** No test is constructed here: the statements hold for every test of the
project with the stated profile. The normalization by the mass of the norm-one quotient in
`sLocalTrace_asymptotic_of_sharp_comparison` is not treated: the action of the test is written
in the norm coordinate. The cutoff is sharp, with no lower cutoff. Order zero and the field `ℚ`
with no finite place only.
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

private theorem ratInfinite_abs (z : K∞) : |r∞ z| = ‖z‖ := by
  rw [← Real.norm_eq_abs, ← dist_zero_right, ← dist_zero_right z, ← map_zero r∞]
  exact (InfinitePlace.Completion.isometryEquivRealOfIsReal Rat.isReal_infinitePlace).dist_eq z 0

/-- The multiplicative measure at the real place of `ℚ` is `dx / |x|` in the real coordinate. -/
theorem integral_ratInfiniteMultiplicative (G : ℝ → ℂ) :
    ∫ u : K∞ˣ, G (r∞ u.val) ∂(infiniteLocalMultiplicativeTamagawaMeasure ℚ Rat.infinitePlace) =
      ∫ x : ℝ, (|x|⁻¹ : ℝ) • G x := by
  let : BorelSpace K∞ := ⟨rfl⟩
  let : BorelSpace K∞ˣ := borelSpace_units_of_continuousInv₀ _
  let e := InfinitePlace.Completion.isometryEquivRealOfIsReal Rat.isReal_infinitePlace
  have hval := (IsOpenUnits.isOpenEmbedding_unitsVal (M := K∞)).measurableEmbedding
  have hmult : Rat.infinitePlace.mult = 1 := Rat.isReal_infinitePlace.mult_eq_one
  let d : K∞ → ENNReal := fun x ↦ (↑(‖x‖₊ ^ Rat.infinitePlace.mult) : ENNReal)⁻¹
  have hd : Measurable d := by fun_prop
  change ∫ u, _ ∂((infiniteLocalAdditiveTamagawaMeasure ℚ Rat.infinitePlace).withDensity
    d).comap Units.val = _
  rw [← hval.integral_map (g := fun y ↦ G (r∞ y)), hval.map_comap,
    setIntegral_withDensity_eq_setIntegral_toReal_smul hd ?_ _ hval.measurableSet_range]
  · rw [setIntegral_eq_integral_of_forall_compl_eq_zero (fun y hy ↦ ?_),
      infiniteLocalAdditiveTamagawaMeasure, dite_eq_left Rat.isReal_infinitePlace]
    · let m := e.symm.toHomeomorph.toMeasurableEquiv
      rw [show ((r∞).symm : ℝ → K∞) = m from rfl, integral_map_equiv]
      refine integral_congr_ae (Eventually.of_forall fun x ↦ ?_)
      have hx : r∞ (m x) = x := (r∞).apply_symm_apply x
      have hn : ‖m x‖ = |x| := by rw [← ratInfinite_abs, hx]
      simp only [d, hmult, pow_one, hx]
      rw [ENNReal.toReal_inv, ENNReal.coe_toReal, coe_nnNorm, hn]
    · have hy0 : y = 0 := by
        by_contra h
        exact hy ⟨Units.mk0 y h, rfl⟩
      simp [d, hy0]
  · refine ae_restrict_of_forall_mem hval.measurableSet_range fun y ⟨u, hu⟩ ↦ ?_
    simp only [d, hmult, pow_one]
    exact ENNReal.inv_lt_top.mpr (by simp [← hu])

/-- The integral over the line of an even profile supported in `±[a, b]` against
`√|x| / (|x| |1 - x|)`, folded onto `[a, b]`. -/
private theorem integral_evenProfile {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (h1 : 1 ∉ Icc a b)
    {φ : ℝ → ℝ} (hφ : ContinuousOn φ (Icc a b)) :
    ∫ x : ℝ, |x|⁻¹ * ((if |x| ∈ Icc a b then φ |x| else 0) * √|x| / |1 - x|) =
      ∫ g in a..b, φ g * (√g / |1 - g| + √g / |1 + g|) / g := by
  have hne0 : ∀ x ∈ Icc a b, x ≠ 0 := fun x hx ↦ (ha.trans_le hx.1).ne'
  have hne1 : ∀ x ∈ Icc a b, |1 - x| ≠ 0 := by
    intro x hx h0
    rw [abs_eq_zero, sub_eq_zero] at h0
    exact h1 (by rw [h0]; exact hx)
  have hne2 : ∀ x ∈ Icc a b, |1 + x| ≠ 0 := by
    intro x hx h0
    rw [abs_eq_zero] at h0
    linarith [ha.trans_le hx.1]
  have hk1 : ContinuousOn (fun x : ℝ ↦ x⁻¹ * (φ x * √x / |1 - x|)) (Icc a b) :=
    (continuousOn_id.inv₀ hne0).mul ((hφ.mul Real.continuous_sqrt.continuousOn).div
      (continuous_const.sub continuous_id).abs.continuousOn hne1)
  have hk2 : ContinuousOn (fun g : ℝ ↦ g⁻¹ * (φ g * √g / |1 + g|)) (Icc a b) :=
    (continuousOn_id.inv₀ hne0).mul ((hφ.mul Real.continuous_sqrt.continuousOn).div
      (continuous_const.add continuous_id).abs.continuousOn hne2)
  have hk2' : ContinuousOn (fun x : ℝ ↦ (-x)⁻¹ * (φ (-x) * √(-x) / |1 + -x|))
      (Icc (-b) (-a)) :=
    hk2.comp continuous_neg.continuousOn fun x hx ↦ ⟨by linarith [hx.2], by linarith [hx.1]⟩
  have hsplit : (fun x : ℝ ↦ |x|⁻¹ * ((if |x| ∈ Icc a b then φ |x| else 0) * √|x| / |1 - x|)) =
      fun x ↦ (Icc a b).indicator (fun x ↦ x⁻¹ * (φ x * √x / |1 - x|)) x +
        (Icc (-b) (-a)).indicator (fun x ↦ (-x)⁻¹ * (φ (-x) * √(-x) / |1 + -x|)) x := by
    funext x
    by_cases hx : x ∈ Icc a b
    · have hpos : 0 < x := ha.trans_le hx.1
      have hneg : x ∉ Icc (-b) (-a) := fun h ↦ by linarith [h.2]
      rw [indicator_of_mem hx, indicator_of_notMem hneg, add_zero, abs_of_pos hpos, ite_eq_left hx]
    · by_cases hx' : x ∈ Icc (-b) (-a)
      · have hneg : x < 0 := by linarith [hx'.2]
        have habs : |x| = -x := abs_of_neg hneg
        have hmem : -x ∈ Icc a b := ⟨by linarith [hx'.2], by linarith [hx'.1]⟩
        rw [indicator_of_notMem hx, indicator_of_mem hx', zero_add, habs, ite_eq_left hmem,
          sub_eq_add_neg]
      · have hno : |x| ∉ Icc a b := by
          intro h
          rcases abs_cases x with ⟨he, _⟩ | ⟨he, _⟩
          · exact hx (he ▸ h)
          · exact hx' ⟨by linarith [h.2], by linarith [h.1]⟩
        rw [indicator_of_notMem hx, indicator_of_notMem hx', ite_eq_right hno]
        simp
  rw [hsplit, integral_add (hk1.integrableOn_Icc.integrable_indicator measurableSet_Icc)
    (hk2'.integrableOn_Icc.integrable_indicator measurableSet_Icc),
    integral_indicator measurableSet_Icc, integral_indicator measurableSet_Icc,
    integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hab,
    integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (neg_le_neg hab),
    intervalIntegral.integral_comp_neg (fun g ↦ g⁻¹ * (φ g * √g / |1 + g|)), neg_neg, neg_neg,
    ← intervalIntegral.integral_add (hk1.intervalIntegrable_of_Icc hab)
      (hk2.intervalIntegrable_of_Icc hab)]
  refine intervalIntegral.integral_congr fun g _ ↦ ?_
  ring

/-- Paper: Definition B.4.4.1(2), p. 620, with (12.5.1.1), p. 520. **The principal value at the
real place of `ℚ` of an even test supported in `±[a, b]`**, with `1` outside `[a, b]`, is the
real-place integral `∫ φ(g) (1/2) (√g / |1 - g| + √g / |1 + g|) dg / g`. -/
theorem ratInfiniteConnesWeilPrincipalValue_eq {a b : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (h1 : 1 ∉ Icc a b) {φ : ℝ → ℝ} (hφ : ContinuousOn φ (Icc a b))
    (f : BruhatCompactSupport K∞ˣ)
    (hf : ∀ u : K∞ˣ, f.val u = if |r∞ u.val| ∈ Icc a b then (φ |r∞ u.val| : ℂ) else 0) :
    infiniteConnesWeilPrincipalValue Rat.infinitePlace f =
      ((∫ g in a..b, φ g * (1 / 2 * (√g / |1 - g| + √g / |1 + g|)) / g : ℝ) : ℂ) := by
  have hf1 : f.val 1 = 0 := by
    rw [hf, ite_eq_right]
    rw [Units.val_one, map_one, abs_one]
    exact h1
  have hpv := realConnesWeilPrincipalValue_of_apply_one_zero Rat.infinitePlace
    Rat.isReal_infinitePlace f hf1
  dsimp only at hpv
  rw [hpv]
  have hint : ∫ u : K∞ˣ, f.val u * (Real.sqrt ‖u.val‖ : ℂ) / ((‖1 - u.val‖ : ℝ) : ℂ)
      ∂(infiniteLocalMultiplicativeTamagawaMeasure ℚ Rat.infinitePlace) =
      ∫ u : K∞ˣ, (fun x : ℝ ↦ (((if |x| ∈ Icc a b then φ |x| else 0) * √|x| / |1 - x| : ℝ) : ℂ))
        (r∞ u.val) ∂(infiniteLocalMultiplicativeTamagawaMeasure ℚ Rat.infinitePlace) := by
    refine integral_congr_ae (Eventually.of_forall fun u ↦ ?_)
    have hn1 : ‖u.val‖ = |r∞ u.val| := (ratInfinite_abs _).symm
    have hn2 : ‖1 - u.val‖ = |1 - r∞ u.val| := by
      rw [← ratInfinite_abs, map_sub, map_one]
    simp only [hf u, hn1, hn2]
    split_ifs <;> push_cast <;> ring
  rw [hint, integral_ratInfiniteMultiplicative
    (fun x : ℝ ↦ (((if |x| ∈ Icc a b then φ |x| else 0) * √|x| / |1 - x| : ℝ) : ℂ))]
  have hreal : ∫ x : ℝ, (|x|⁻¹ : ℝ) •
      (((if |x| ∈ Icc a b then φ |x| else 0) * √|x| / |1 - x| : ℝ) : ℂ) =
      ((∫ x : ℝ, |x|⁻¹ * ((if |x| ∈ Icc a b then φ |x| else 0) * √|x| / |1 - x|) : ℝ) : ℂ) := by
    rw [← integral_complex_ofReal]
    refine integral_congr_ae (Eventually.of_forall fun x ↦ ?_)
    simp only [Complex.real_smul, Complex.ofReal_mul]
  rw [hreal, integral_evenProfile ha hab h1 hφ]
  have hfin : ∫ g in a..b, φ g * (1 / 2 * (√g / |1 - g| + √g / |1 + g|)) / g =
      1 / 2 * ∫ g in a..b, φ g * (√g / |1 - g| + √g / |1 + g|) / g := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun g _ ↦ ?_
    ring
  rw [hfin]
  push_cast
  ring

/-! ### The limit of the traces and the principal value of the project -/

local notation "mₛ(" F ", " S ")" =>
  (continuousSIdeleQuotientNorm F S :
    SIdeleQuotient F S →ₜ* ℝ≥0ˣ)
local notation "μₛ(" F ", " S ")" => sLocalQuotientTamagawaMeasure F S
local notation "localMeasure(" F ", " S ", " s ")" =>
  (μₛ(F, S)).withDensity (fun g ↦
    ENNReal.ofReal (intervalSobolevDensity 0 0 s (Real.log (((mₛ(F, S)) g).val : ℝ))))
local notation "J₀" => SIdeleQuotient ℚ ∅
local notation "W₀" => Lp ℂ 2 (localMeasure(ℚ, ∅, 0))
local notation "normℝ(" g ")" => (((sIdeleQuotientNorm ℚ ∅ g : ℝ≥0ˣ) : ℝ≥0) : ℝ)
local notation "level₀(" ω ", " Y ")" =>
  sLocalInvariantPWSobolev (F := ℚ) (S := ∅) (s := 0) le_rfl (a := 1 / 2) (by norm_num) ω Y

attribute [local instance] instIdeleClassMeasurableSpaceSec1 instIdeleClassBorelSpaceSec1
  instIdeleClassT2Sec1 instIdeleClassLocallyCompactSec1 instIdeleClassSecondCountableSec1
  instIdeleClassHaarMeasureSec1 instSIdeleQuotientMeasurableSpaceSec1

section Limit

variable {ι : Type*} {l : Filter ι} [l.IsCountablyGenerated] {Ys Ls : ι → ℝ}

/-- Paper: Theorem 12.4.1.1, pp. 514–519, with Definition B.4.4.1(2), p. 620. **The limit of
the traces is the principal value of the project minus one integral.** Over `ℚ` with no finite
place, at order zero and twist `1/2`, let `f` be a test at the real place that is even and
supported in `±[a, b]`, with profile `φ` and `1` outside `[a, b]`. The Hilbert traces of
`P_Y ∘ χ_L ∘ A ∘ P_Y` on the level of the project tend, as `Y * L → ∞`, to
`infiniteConnesWeilPrincipalValue` of `f` minus `∫ φ(g) min(g^(1/2), g^(-1/2)) d×g`.
Reconstruction: as for `ratEmpty_hilbertTrace_average_compression`. For `F = ℚ` and `S = ∅` the
sum `principalValues` of `sLocalTrace_asymptotic_of_sharp_comparison` is this one principal
value. -/
theorem ratEmpty_tendsto_hilbertTrace_principalValue_sub
    (ω : PontryaginDual (sIdeleQuotientNorm ℚ ∅).ker) {a b : ℝ} {φ : ℝ → ℝ} (ha : 0 < a)
    (hab : a ≤ b) (h1 : 1 ∉ Icc a b) (hφ : ContinuousOn φ (Icc a b)) (σ : ℝ → J₀)
    (hσ : ∀ t : ℝ, 0 < t → normℝ(σ t) = t) (hY : ∀ i, 0 < Ys i) (hL : ∀ i, 0 ≤ Ls i)
    (hYL : Tendsto (fun i ↦ Ys i * Ls i) l atTop) (f : BruhatCompactSupport K∞ˣ)
    (hf : ∀ u : K∞ˣ, f.val u = if |r∞ u.val| ∈ Icc a b then (φ |r∞ u.val| : ℂ) else 0) :
    ∃ A : W₀ →L[ℂ] W₀,
      (∀ F : W₀, A F = ∫ t in a..b, ((φ t / t : ℝ) : ℂ) • ratEmptyTranslation (σ t) F) ∧
      ∃ tr : ι → ℂ,
        (∀ i, ∃ hn : IsNuclearOperator ((level₀(ω, Ys i)).starProjection ∘L
            ratEmptyCutoff (Ls i) ∘L A ∘L (level₀(ω, Ys i)).starProjection),
          hilbertTrace ⟨(level₀(ω, Ys i)).starProjection ∘L ratEmptyCutoff (Ls i) ∘L A ∘L
            (level₀(ω, Ys i)).starProjection, hn⟩ = tr i) ∧
        Tendsto tr l (𝓝 (infiniteConnesWeilPrincipalValue Rat.infinitePlace f -
          ((∫ g in a..b, φ g * min (√g) (√g)⁻¹ / g : ℝ) : ℂ))) := by
  have h := ratEmpty_tendsto_hilbertTrace_average_compression ω ha hab h1 hφ σ hσ hY hL hYL
  obtain ⟨A, hA, tr, htr, hlim⟩ := h
  refine ⟨A, hA, tr, htr, ?_⟩
  rw [ratInfiniteConnesWeilPrincipalValue_eq ha hab h1 hφ f hf, ← Complex.ofReal_sub]
  exact hlim

/-- Paper: Theorem 12.4.1.1, pp. 514–519. **The traces do not tend to the principal value.**
In the setting of `ratEmpty_tendsto_hilbertTrace_principalValue_sub`, if
`∫ φ(g) min(g^(1/2), g^(-1/2)) d×g` is not zero, the Hilbert traces of `P_Y ∘ χ_L ∘ A ∘ P_Y` on
the level of the project do not tend to `infiniteConnesWeilPrincipalValue` of the test.
Reconstruction: the paper asserts this limit without specifying its cutoffs. The statement here
is for the sharp cutoff to norm at most `L` and no lower cutoff. -/
theorem ratEmpty_not_tendsto_hilbertTrace_principalValue [l.NeBot]
    (ω : PontryaginDual (sIdeleQuotientNorm ℚ ∅).ker) {a b : ℝ} {φ : ℝ → ℝ} (ha : 0 < a)
    (hab : a ≤ b) (h1 : 1 ∉ Icc a b) (hφ : ContinuousOn φ (Icc a b)) (σ : ℝ → J₀)
    (hσ : ∀ t : ℝ, 0 < t → normℝ(σ t) = t) (hY : ∀ i, 0 < Ys i) (hL : ∀ i, 0 ≤ Ls i)
    (hYL : Tendsto (fun i ↦ Ys i * Ls i) l atTop) (f : BruhatCompactSupport K∞ˣ)
    (hf : ∀ u : K∞ˣ, f.val u = if |r∞ u.val| ∈ Icc a b then (φ |r∞ u.val| : ℂ) else 0)
    (hD : ∫ g in a..b, φ g * min (√g) (√g)⁻¹ / g ≠ 0) :
    ∃ A : W₀ →L[ℂ] W₀,
      (∀ F : W₀, A F = ∫ t in a..b, ((φ t / t : ℝ) : ℂ) • ratEmptyTranslation (σ t) F) ∧
      ∃ tr : ι → ℂ,
        (∀ i, ∃ hn : IsNuclearOperator ((level₀(ω, Ys i)).starProjection ∘L
            ratEmptyCutoff (Ls i) ∘L A ∘L (level₀(ω, Ys i)).starProjection),
          hilbertTrace ⟨(level₀(ω, Ys i)).starProjection ∘L ratEmptyCutoff (Ls i) ∘L A ∘L
            (level₀(ω, Ys i)).starProjection, hn⟩ = tr i) ∧
        ¬ Tendsto tr l (𝓝 (infiniteConnesWeilPrincipalValue Rat.infinitePlace f)) := by
  have h := ratEmpty_tendsto_hilbertTrace_principalValue_sub ω ha hab h1 hφ σ hσ hY hL hYL f hf
  obtain ⟨A, hA, tr, htr, hlim⟩ := h
  refine ⟨A, hA, tr, htr, fun hpv ↦ hD ?_⟩
  have heq := tendsto_nhds_unique hpv hlim
  have hz : ((∫ g in a..b, φ g * min (√g) (√g)⁻¹ / g : ℝ) : ℂ) = 0 := by
    linear_combination heq
  exact_mod_cast hz

end Limit

end RiemannMasullo
