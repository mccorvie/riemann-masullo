module

public import RiemannMasullo.Ch01_Introduction.Sec4_TranslatedFirstPrimes
public import RiemannMasullo.ForMathlib.Analysis.Complex.AbelSquareMean
public import RiemannMasullo.ForMathlib.Analysis.Fourier.StripLaplace
import RiemannMasullo.Ch12_TraceGeometric.Sec5
import RiemannMasullo.ForMathlib.Analysis.Complex.AbelExpSeries
import RiemannMasullo.ForMathlib.Analysis.Complex.ExpSumGrowth
import Mathlib.MeasureTheory.Constructions.Polish.Basic

/-! # Signed degree-one prime sums and the full divisor on translates

The translated explicit formula of Theorem B.4.4.7 (p. 623) identifies the
centered first-prime sum, up to bounded error, with a single character's
negative exponential series. At each positive threshold the squared Abel
mean measures the full multiplicities of the distinct zeros on its edge.
-/

@[expose] public noncomputable section

open Classical Filter Function IsDedekindDomain MeasureTheory NumberField Set
open scoped NNReal NumberField.AdeleRing Topology ContDiff

namespace RiemannMasullo

set_option quotPrecheck false
attribute [local instance] instIdeleClassMeasurableSpaceSec1 instIdeleClassBorelSpaceSec1
  instIdeleClassT2Sec1 instIdeleClassLocallyCompactSec1 instIdeleClassSecondCountableSec1
  instIdeleClassHaarMeasureSec1 instFiniteCompletionUnitsLocallyCompactSec4b
variable {F : Type*} [Field F] [NumberField F]
local notation "G" => IdeleClassGroup (𝓞 F) F
local notation "U" => PontryaginDual G
local notation "V" => HeightOneSpectrum (𝓞 F)
local notation "volumeOne" => ((normOneIdeleClassTamagawaMeasure F) univ).toReal
local notation "ord(" χ ", " z ")" => MeromorphicOn.divisor (continuedCompletedHeckeL (F := F) χ) univ z
local notation "Z(" χ ")" => {ρ : ℂ // 0 < ord(χ, ρ)}

/-- Full-order, volume-normalized coefficient in the translated arithmetic expansion. -/
def firstPrimeFullCoefficient (χ : U) (H : ℝ → ℂ) (ρ : ℂ) : ℂ :=
  (ord(χ, ρ) : ℂ) * bilateralLaplace H (ρ - 1 / 2)

/-- The sum of the squared full-multiplicity coefficients at the prescribed right edge. -/
def firstPrimeBoundaryMass (χ : U) (H : ℝ → ℂ) (c : ℝ) : ℝ :=
  ∑' ρ : Z(χ), if ρ.val.re - 1 / 2 = c then ‖firstPrimeFullCoefficient χ H ρ.val‖ ^ 2 else 0

/-- Each full multiplicity contributes its actual square to the boundary mass. -/
theorem firstPrimeBoundaryMass_eq (χ : U) (H : ℝ → ℂ) (c : ℝ) :
    firstPrimeBoundaryMass χ H c = ∑' ρ : Z(χ),
      if ρ.val.re - 1 / 2 = c then (ord(χ, ρ.val) : ℝ) ^ 2 * ‖bilateralLaplace H (ρ.val - 1 / 2)‖ ^ 2 else 0 := by
  unfold firstPrimeBoundaryMass
  apply tsum_congr
  intro ρ
  simp only [firstPrimeFullCoefficient, norm_mul, mul_pow, Complex.norm_int_of_nonneg ρ.property.le]

/-- Positive sites of the full completed divisor form a countable type. -/
private theorem firstPrime_fullDivisor_countable (χ : U) : Countable Z(χ) := by
  let S : Set ℂ := {ρ | 0 < ord(χ, ρ)}
  have hD := (MeromorphicOn.divisor (continuedCompletedHeckeL (F := F) χ) univ).eq_zero_codiscreteWithin
  have he : Sᶜ ∈ codiscrete ℂ := by
    filter_upwards [hD] with z hz
    exact fun hp ↦ hp.ne' hz
  let : DiscreteTopology S := isDiscrete_iff_discreteTopology.mp (compl_mem_codiscrete_iff.mp he).2
  exact countable_of_Lindelof_of_discrete (X := S)

/-- Paper: Theorem B.4.4.7, p. 623. The physical centered sum is within a fixed distance of the negative full
spectral series on the half-line. All multiplicities and the inverse character are retained. -/
theorem firstPrime_fullSeries_bounded_error (τ : ℝ≥0ˣ →ₜ* G)
    (hτ : RightInverse τ (ideleClassNorm F)) (ψ : U) (hψ : ∀ t, ψ (τ t) = 1)
    (H : ℝ → ℂ) (hH : ContDiff ℝ (∞) H) {u v : ℝ}
    (hu : 0 < u) (huv : u ≤ v) (hs : tsupport H ⊆ Icc u v) :
    (Summable fun ρ : Z(ψ⁻¹) ↦ ‖firstPrimeFullCoefficient ψ⁻¹ H ρ.val‖) ∧
    ∃ C ≥ (0 : ℝ), ∀ y ≥ (0 : ℝ), ‖firstPrimeDegreeOneSum ψ⁻¹ H y v -
      firstPrimePolarMoment ψ H y (1 / 2) +
      ∑' ρ : Z(ψ⁻¹), firstPrimeFullCoefficient ψ⁻¹ H ρ.val * Complex.exp ((ρ.val - 1 / 2) * y)‖ ≤ C := by
  have hc : HasCompactSupport H := HasCompactSupport.intro isCompact_Icc
    (fun x hx ↦ image_eq_zero_of_notMem_tsupport fun h ↦ hx (hs h))
  have hV : (volumeOne : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (firstPrime_volume_pos (F := F)).ne'
  choose φ hφ using fun y : ℝ ↦ exists_characterNormTest (F := F) ψ (fun x ↦ H (x - y))
    (hH.comp (contDiff_id.sub contDiff_const)) (hc.comp_homeomorph (Homeomorph.subRight y))
  let A (y : ℝ) (w : InfinitePlace F) := (idelicExplicitFormula_infiniteTestMap (F := F) w).choose (φ y)
  let B (y : ℝ) (w : V) := (idelicExplicitFormula_finiteTestMap (F := F) w).choose (φ y)
  have hA (y : ℝ) (w : InfinitePlace F) (t) : (A y w).val t =
      (φ y).val (IdeleClassGroup.ofCompletion (𝓞 F) F w t) :=
    (idelicExplicitFormula_infiniteTestMap (F := F) w).choose_spec (φ y) t
  have hB (y : ℝ) (w : V) (t) : (B y w).val t =
      (φ y).val (IdeleClassGroup.ofAdicCompletion (𝓞 F) F w t) :=
    (idelicExplicitFormula_finiteTestMap (F := F) w).choose_spec (φ y) t
  have he (y : ℝ) : HasSum (fun ρ : Z(ψ⁻¹) ↦ firstPrimeFullCoefficient ψ⁻¹ H ρ.val *
      Complex.exp ((ρ.val - 1 / 2) * y)) (firstPrimeLocalTerms (φ y) (A y) (B y) / (volumeOne : ℂ)) := by
    have ht := (translatedLocalTerms_hasSum τ hτ ψ hψ H hH hc y (φ y) (hφ y) (A y) (B y)
      (hA y) (hB y)).div_const (volumeOne : ℂ)
    apply ht.congr_fun
    intro ρ
    symm
    change ((ord(ψ⁻¹, ρ.val) : ℂ) * ((volumeOne : ℂ) * bilateralLaplace H (ρ.val - 1 / 2)) *
      Complex.exp ((ρ.val - 1 / 2) * y)) / (volumeOne : ℂ) = _
    rw [div_eq_iff hV]
    dsimp only [firstPrimeFullCoefficient]
    ring
  refine ⟨?_, ?_⟩
  · simpa only [Complex.ofReal_zero, mul_zero, Complex.exp_zero, mul_one] using (he 0).summable.norm
  · obtain ⟨C, hC, h⟩ := firstPrime_centered_localTerms_uniform τ hτ ψ hψ H hH.continuous hu huv hs
    refine ⟨C, hC, fun y hy ↦ ?_⟩
    rw [(he y).tsum_eq]
    exact h y hy (φ y) (hφ y) (A y) (B y) (hA y) (hB y)

private theorem firstPrime_centered_measurable (ψ : U) (H : ℝ → ℂ) (hH : Measurable H) (v : ℝ) :
    Measurable (fun y ↦ firstPrimeDegreeOneSum ψ⁻¹ H y v - firstPrimePolarMoment ψ H y (1 / 2)) := by
  apply (firstPrimeDegreeOneSum_measurable ψ⁻¹ H hH v).sub
  by_cases h : ψ = 1
  · simp only [firstPrimePolarMoment, ite_eq_left h]
    fun_prop
  · simp only [firstPrimePolarMoment, ite_eq_right h]
    exact measurable_const

private theorem firstPrime_fullDivisor_separated (χ : U) (z : ℂ) :
    ∀ᶠ s in 𝓝[≠] z, s ∉ range (fun ρ : Z(χ) ↦ ρ.val - 1 / 2) := by
  have hD := (MeromorphicOn.divisor (continuedCompletedHeckeL (F := F) χ) univ).eq_zero_codiscreteWithin
  have h := (mem_codiscreteWithin_iff_forall_mem_nhdsNE.mp hD) (z + 1 / 2) (mem_univ _)
  rw [compl_univ, union_empty] at h
  have ht : Tendsto (fun s : ℂ ↦ s + 1 / 2) (𝓝[≠] z) (𝓝[≠] (z + 1 / 2)) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨((continuous_id.add continuous_const).tendsto z).mono_left
      nhdsWithin_le_nhds, ?_⟩
    filter_upwards [self_mem_nhdsWithin] with a ha
    exact fun h' ↦ ha (add_right_cancel h')
  filter_upwards [ht.eventually h] with s hzero
  rintro ⟨z', rfl⟩
  change ord(χ, z'.val - 1 / 2 + 1 / 2) = (0 : ℤ) at hzero
  rw [sub_add_cancel] at hzero
  exact z'.property.ne' hzero

/-- A finite weighted second moment of the centered physical prime sum forces the
test transform to vanish at each genuine divisor site strictly beyond that exponent. -/
theorem firstPrime_moment_eq_zero_of_integrableOn_square (τ : ℝ≥0ˣ →ₜ* G)
    (hτ : RightInverse τ (ideleClassNorm F)) (ψ : U) (hψ : ∀ t, ψ (τ t) = 1)
    (H : ℝ → ℂ) (hH : ContDiff ℝ (∞) H) {u v q : ℝ}
    (hu : 0 < u) (huv : u ≤ v) (hs : tsupport H ⊆ Icc u v) (hq : 0 ≤ q)
    (hL : IntegrableOn (fun y : ℝ ↦ ‖firstPrimeDegreeOneSum ψ⁻¹ H y v -
      firstPrimePolarMoment ψ H y (1 / 2)‖ ^ 2 * Real.exp (-(2 * q) * y)) (Ici 0)) :
    ∀ ρ : ℂ, 0 < ord(ψ⁻¹, ρ) → q < ρ.re - 1 / 2 → bilateralLaplace H (ρ - 1 / 2) = 0 := by
  let w (z : Z(ψ⁻¹)) := z.val - 1 / 2
  let b (z : Z(ψ⁻¹)) := firstPrimeFullCoefficient ψ⁻¹ H z.val
  let S (y : ℝ) := ∑' z, b z * Complex.exp (w z * y)
  let f (y : ℝ) := firstPrimeDegreeOneSum ψ⁻¹ H y v - firstPrimePolarMoment ψ H y (1 / 2)
  obtain ⟨hb, C, _, hC⟩ := firstPrime_fullSeries_bounded_error τ hτ ψ hψ H hH hu huv hs
  have hi : Injective w := fun _ _ h ↦ Subtype.ext (sub_left_inj.mp h)
  have hr (z : Z(ψ⁻¹)) : (w z).re ≤ 1 / 2 := by
    have hh := (explicitFormulaCompletedHeckeL_zero_re_mem ψ⁻¹ z.property).2
    change (z.val - 1 / 2).re ≤ _
    rw [Complex.sub_re]
    norm_num
    linarith
  have he (y : ℝ) (hy : 0 ≤ y) : HasSum (fun z ↦ b z * Complex.exp (w z * y)) (S y) :=
    (AbelEdge.summable_norm_expSeries w b hr hb y hy).of_norm.hasSum
  have hD (y : ℝ) (hy : 0 ≤ y) : ‖S y‖ ≤ ‖f y‖ + C := by
    have hpair : ‖f y + S y‖ ≤ C := hC y hy
    calc
      ‖S y‖ = ‖(f y + S y) - f y‖ := by rw [add_sub_cancel_left]
      _ ≤ ‖f y + S y‖ + ‖f y‖ := norm_sub_le _ _
      _ ≤ ‖f y‖ + C := by linarith
  have hf := firstPrime_centered_measurable ψ H hH.continuous.measurable v
  have hDi (σ : ℝ) (hσ : q < σ) :
      IntegrableOn (fun y ↦ (‖f y‖ + C) * Real.exp (-σ * y)) (Ioi 0) := by
    have h1 := AbelEdge.integrableOn_norm_mul_exp_of_sq_mul_exp hf hσ hL
    have h2 := (integrableOn_exp_mul_Ioi (neg_neg_of_pos (hq.trans_lt hσ)) 0).const_mul C
    apply ((Iff.mp integrableOn_Ici_iff_integrableOn_Ioi h1).add h2).congr_fun _ measurableSet_Ioi
    intro y _
    simp only [Pi.add_apply, add_mul, f]
  intro ρ hρ hqρ
  let z : Z(ψ⁻¹) := ⟨ρ, hρ⟩
  have hwρ : q < (w z).re := by simpa [w, z, Complex.sub_re] using hqρ
  have hzero := eq_zero_of_hasSum_exp_of_integrable w b hi (firstPrime_fullDivisor_separated ψ⁻¹)
    hr hb.of_norm S he (fun y ↦ ‖f y‖ + C) hD hDi z hwρ
  have hm : (ord(ψ⁻¹, ρ) : ℂ) ≠ 0 := by exact_mod_cast hρ.ne'
  exact (mul_eq_zero.mp hzero).resolve_left hm

/-- For any smooth positive-log-support profile, absence of strictly exterior sites gives
the exact full-multiplicity edge mass for the centered, physical degree-one prime sum. -/
theorem firstPrime_centered_tendsto_abelBoundaryMass (τ : ℝ≥0ˣ →ₜ* G)
    (hτ : RightInverse τ (ideleClassNorm F)) (ψ : U) (hψ : ∀ t, ψ (τ t) = 1)
    (H : ℝ → ℂ) (hH : ContDiff ℝ (∞) H) {u v c : ℝ}
    (hu : 0 < u) (huv : u ≤ v) (hs : tsupport H ⊆ Icc u v) (hc : 0 < c)
    (hr : ∀ ρ : ℂ, 0 < ord(ψ⁻¹, ρ) → ρ.re - 1 / 2 ≤ c) :
    Tendsto (fun ε : ℝ ↦ AbelEdge.weightedSquareAbelMean (fun y ↦
      firstPrimeDegreeOneSum ψ⁻¹ H y v - firstPrimePolarMoment ψ H y (1 / 2)) c ε)
      (𝓝[>] 0) (𝓝 (ENNReal.ofReal (firstPrimeBoundaryMass ψ⁻¹ H c))) := by
  let : Countable Z(ψ⁻¹) := firstPrime_fullDivisor_countable ψ⁻¹
  let w (z : Z(ψ⁻¹)) := z.val - 1 / 2
  let b (z : Z(ψ⁻¹)) := firstPrimeFullCoefficient ψ⁻¹ H z.val
  let f (y : ℝ) := firstPrimeDegreeOneSum ψ⁻¹ H y v - firstPrimePolarMoment ψ H y (1 / 2)
  let g (y : ℝ) := -(∑' z, b z * Complex.exp (w z * y))
  have hwre (z : Z(ψ⁻¹)) : (w z).re = z.val.re - 1 / 2 := by simp [w, Complex.sub_re]
  have hw (z : Z(ψ⁻¹)) : (w z).re ≤ c := (hwre z).trans_le (hr z.val z.property)
  have hi : Injective w := fun _ _ hh ↦ Subtype.ext (sub_left_inj.mp hh)
  have hf : Measurable f := firstPrime_centered_measurable ψ H hH.continuous.measurable v
  have hm : Measurable (fun y : ℝ ↦ ∑' z, b z * Complex.exp (w z * y)) :=
    Measurable.tsum fun _ ↦ by fun_prop
  have hg : Measurable g := hm.neg
  obtain ⟨hb, C, _, hC⟩ := firstPrime_fullSeries_bounded_error τ hτ ψ hψ H hH hu huv hs
  have hdist (y : ℝ) (hy : 0 ≤ y) : ‖f y - g y‖ ≤ C := by
    simpa only [f, g, b, w, sub_neg_eq_add] using hC y hy
  have hG (y : ℝ) (hy : 0 ≤ y) : ‖g y‖ ≤ (∑' z, ‖b z‖) * Real.exp (c * y) := by
    simpa only [g, norm_neg] using AbelEdge.norm_expSeries_le w b hw hb y hy
  have hlim := AbelEdge.tendsto_abel_normSq_expSeries w b c hi hw hb
  have hM : Tendsto (fun ε : ℝ ↦ ε * ∫ y : ℝ in Ioi 0,
      Real.exp (-(ε + 2 * c) * y) * ‖g y‖ ^ 2) (𝓝[>] 0) (𝓝 (firstPrimeBoundaryMass ψ⁻¹ H c)) := by
    simpa only [g, norm_neg, firstPrimeBoundaryMass, hwre, b] using hlim
  exact AbelEdge.tendsto_ennreal_abel_square_of_bounded_sub hf hg hc hdist hG hM

end RiemannMasullo
