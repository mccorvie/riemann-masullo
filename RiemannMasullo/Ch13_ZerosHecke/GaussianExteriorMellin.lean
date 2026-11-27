module

public import RiemannMasullo.Ch13_ZerosHecke.GaussianDedekindDivisor
import RiemannMasullo.AppB_AnalyticNT.Sec4b

/-!
# The Gaussian trivial-character exterior Mellin sum

For a compactly supported Bruhat test on the idele classes of the Gaussian field,
the exterior sum for the completed trivial character splits into the ordinary zero
sums for Riemann zeta and the quadratic character modulo four. Both factor sums
converge absolutely. They use the same Mellin transform on the Gaussian idele
classes, and a shared zero contributes both of its multiplicities.
-/

public noncomputable section

open Filter MeasureTheory NumberField Set
open scoped NNReal

namespace RiemannMasullo

attribute [local instance] instIdeleClassMeasurableSpaceSec1 instIdeleClassT2Sec1
  instIdeleClassLocallyCompactSec1 instIdeleClassSecondCountableSec1 instIdeleClassBorelSpaceSec1
  instIdeleClassHaarMeasureSec1

local notation "K" => CyclotomicField 4 ℚ
local notation "C₄" => IdeleClassGroup (𝓞 K) K
local notation "L₄" => continuedCompletedHeckeL (1 : PontryaginDual C₄)
local notation "β₄" => gaussianQuadraticCharacter.LFunction
local notation "D(" f ", " s ")" => MeromorphicOn.divisor f univ s
local notation "zeros(" f ", " a ")" =>
  {s : ℂ // (0 < Complex.re s ∧ Complex.re s < 1 ∧ a ≤ |Complex.re s - 1 / 2|) ∧ f s = 0}
local notation "exterior(" a ")" => {s : ℂ // 0 < D(L₄, s) ∧ a ≤ |Complex.re s - 1 / 2|}
local notation "M(" φ ", " s ")" =>
  modulatedFourierMellin (continuousIdeleClassNorm K) univ
    (And.intro (isProperMap_ideleClassNorm K) (ideleClassNorm_ne_one (F := K)))
    (ideleClassTamagawaMeasure K) (Subtype.val (φ : BruhatCompactSupport C₄))
    (ideleClassNormTwist (F := K) 1 ((s : ℂ) - 1 / 2))
local notation "zeroTerm(" f ", " φ ", " s ")" => (D(f, s) : ℂ) * M(φ, s)

private theorem gaussianExteriorMellin_full_summable (φ : BruhatCompactSupport C₄) :
    Summable (fun z : {s : ℂ // 0 < D(L₄, s)} ↦ ‖zeroTerm(L₄, φ, z.val)‖) := by
  have hM (s : ℂ) : M(φ, s) = ∫ g, φ.val g * ideleClassNormTwist (F := K) 1 s g *
      (((ideleClassNorm K g).val : ℝ) : ℂ) ^ (-1 / 2 : ℂ) ∂ideleClassTamagawaMeasure K := by
    unfold modulatedFourierMellin
    rw [Set.indicator_of_mem (by simp [relativeVerticalStrip])]
    apply integral_congr_ae
    filter_upwards with g
    let r : ℂ := ((ideleClassNorm K g).val : ℝ)
    have hr : r ≠ 0 := Complex.ofReal_ne_zero.mpr
      (NNReal.coe_pos.mpr (Units.zero_lt (ideleClassNorm K g))).ne'
    change φ.val g * (1 * r ^ (s - 1 / 2)) = φ.val g * (1 * r ^ s) * r ^ (-1 / 2 : ℂ)
    rw [sub_eq_add_neg, Complex.cpow_add _ _ hr, neg_div]
    ring
  have hf := idelicExplicitFormula_summable_spectral_fiber (F := K) φ (1 : PontryaginDual C₄)
  rw [show explicitFormulaCompletedHeckeL (1 : PontryaginDual C₄) = L₄ from rfl] at hf
  simp_rw [hM]
  exact hf

private theorem gaussianExteriorMellin_divisors_nonneg {s : ℂ} (hs : s.re < 1) :
    0 ≤ D(riemannZeta, s) ∧ 0 ≤ D(β₄, s) := by
  have hne : s ≠ 1 := fun h ↦ by simp [h] at hs
  have hm : MeromorphicOn riemannZeta univ := by
    simpa only [DirichletCharacter.LFunction_modOne_eq] using
      meromorphic_dirichletLFunction (1 : DirichletCharacter ℂ 1)
  rw [MeromorphicOn.divisor_apply hm (mem_univ s),
    MeromorphicOn.divisor_apply (meromorphic_dirichletLFunction gaussianQuadraticCharacter) (mem_univ s)]
  exact ⟨WithTop.untop₀_nonneg.mpr (analyticOn_riemannZeta s hne).meromorphicOrderAt_nonneg,
    WithTop.untop₀_nonneg.mpr ((DirichletCharacter.differentiable_LFunction
      gaussianQuadraticCharacter_ne_one).analyticAt s).meromorphicOrderAt_nonneg⟩

/-- Paper: Lemma B.4.4.9, pp. 624–625. Deviation: each ordinary factor of
Gaussian Dedekind zeta has an absolutely convergent exterior Mellin sum with
its own multiplicities and the test on the Gaussian idele classes. -/
theorem gaussianExteriorMellin_factor_summable (φ : BruhatCompactSupport C₄) (α : ℝ) :
    Summable (fun z : zeros(riemannZeta, α) ↦ ‖zeroTerm(riemannZeta, φ, z.val)‖) ∧
    Summable (fun z : zeros(β₄, α) ↦ ‖zeroTerm(β₄, φ, z.val)‖) := by
  have H := gaussianExteriorMellin_full_summable φ
  have factor (g : ℂ → ℂ) (hz : ∀ s, g s = 0 → riemannZeta s = 0 ∨ β₄ s = 0)
      (hd : ∀ s : ℂ, 0 < s.re → s.re < 1 → 0 ≤ D(g, s) ∧ D(g, s) ≤ D(L₄, s)) :
      Summable (fun z : zeros(g, α) ↦ ‖zeroTerm(g, φ, z.val)‖) := by
    let i (z : zeros(g, α)) : {s : ℂ // 0 < D(L₄, s)} :=
      ⟨z.val, (gaussianCompletedDivisor_pos_iff z.property.1.1 z.property.1.2.1).mpr
        (hz z.val z.property.2)⟩
    have hi : Function.Injective i := fun _ _ h ↦
      Subtype.ext (congrArg (fun z : {s : ℂ // 0 < D(L₄, s)} ↦ z.val) h)
    refine (H.comp_injective hi).of_nonneg_of_le (fun _ ↦ norm_nonneg _) (fun z ↦ ?_)
    obtain ⟨h₀, hle⟩ := hd z.val z.property.1.1 z.property.1.2.1
    change ‖zeroTerm(g, φ, z.val)‖ ≤ ‖zeroTerm(L₄, φ, z.val)‖
    rw [norm_mul, norm_mul, Complex.norm_int_of_nonneg h₀, Complex.norm_int_of_nonneg (h₀.trans hle)]
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast hle) (norm_nonneg _)
  constructor
  · apply factor riemannZeta (fun _ h ↦ Or.inl h)
    intro s h₀ h₁
    obtain ⟨hz, hb⟩ := gaussianExteriorMellin_divisors_nonneg h₁
    exact ⟨hz, (gaussianCompletedDivisor_eq h₀).symm ▸ le_add_of_nonneg_right hb⟩
  · apply factor β₄ (fun _ h ↦ Or.inr h)
    intro s h₀ h₁
    obtain ⟨hz, hb⟩ := gaussianExteriorMellin_divisors_nonneg h₁
    exact ⟨hb, (gaussianCompletedDivisor_eq h₀).symm ▸ le_add_of_nonneg_left hz⟩

/-- Paper: Theorem 12.5.1.1, pp. 519–520. Deviation: on the Gaussian trivial
character the exterior Mellin row has sum equal to the sum of the ordinary
Riemann and quadratic Dirichlet exterior rows at every half-width. -/
theorem gaussianExteriorMellin_hasSum (φ : BruhatCompactSupport C₄) (α : ℝ) :
    HasSum (fun z : exterior(α) ↦ zeroTerm(L₄, φ, z.val))
      ((∑' z : zeros(riemannZeta, α), zeroTerm(riemannZeta, φ, z.val)) +
       (∑' z : zeros(β₄, α), zeroTerm(β₄, φ, z.val))) := by
  obtain ⟨hζ, hχ⟩ := gaussianExteriorMellin_factor_summable φ α
  exact hasSum_trivialHeckeExterior_of_dedekindZeta_eq_mul K gaussianQuadraticCharacter
    (fun _ ↦ gaussianDedekindZeta_eq_product) α (fun s ↦ M(φ, s)) _ _
    (summable_norm_iff.mp hζ).hasSum (summable_norm_iff.mp hχ).hasSum

/-- The exterior Mellin sum on the Gaussian trivial character equals the two
ordinary exterior sums, including all boundary zeros at the chosen half-width. -/
theorem gaussianExteriorMellin_tsum_eq (φ : BruhatCompactSupport C₄) (α : ℝ) :
    (∑' z : exterior(α), zeroTerm(L₄, φ, z.val)) =
      (∑' z : zeros(riemannZeta, α), zeroTerm(riemannZeta, φ, z.val)) +
      (∑' z : zeros(β₄, α), zeroTerm(β₄, φ, z.val)) :=
  (gaussianExteriorMellin_hasSum φ α).tsum_eq

end RiemannMasullo
