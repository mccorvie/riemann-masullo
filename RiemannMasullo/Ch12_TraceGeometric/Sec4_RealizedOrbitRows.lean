module

public import RiemannMasullo.Ch12_TraceGeometric.Sec4_FixedAnnulusOrbit
import RiemannMasullo.Ch12_TraceGeometric.Sec4_OrbitUnfolding
import RiemannMasullo.Ch12_TraceGeometric.Sec4_AngularConvolutionSupport
import RiemannMasullo.Ch09_HardySobolev.Sec3
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! # Concrete rows of the fixed-annulus orbit kernel -/

public noncomputable section

open Classical Filter Function IsDedekindDomain MeasureTheory NumberField Set
open scoped BigOperators ContDiff ENNReal NNReal NumberField.AdeleRing SchwartzMap Topology

namespace RiemannMasullo

set_option maxSynthPendingDepth 8

variable {F : Type*} [Field F] [NumberField F]
  {S : Finset (HeightOneSpectrum (𝓞 F))}

local notation "Aₛ" => SAdeleRing F S
local notation "Iₛ" => (SAdeleRing F S)ˣ
local notation "Jₛ" => SIdeleQuotient F S
local notation "Hₛ" => sProjectedDiagonal F S
set_option quotPrecheck false in
local notation "normS(" x ")" => (((sIdeleNorm F S x).val : ℝ))
local notation "νₛ" => sAdditiveTamagawaMeasure F S
local notation "μₛ" => sMultiplicativeTamagawaMeasure F S
local notation "μJ" => sLocalQuotientTamagawaMeasure F S
local notation "testₛ" => SchwartzBruhat (Multiplicative Aₛ)
local notation "testAt(" f "," x ")" => (f : testₛ) (Multiplicative.ofAdd x)

attribute [local instance] instSIdeleQuotientMeasurableSpaceSec1
  instSIdeleQuotientBorelSpaceSec1 instSIdeleQuotientT2Sec1 instSIdeleQuotientLocallyCompactSec1
  instSIdeleQuotientSecondCountableSec1 instSIdeleQuotientHaarMeasureSec1
  instNormOneSIdeleQuotientMeasurableSpaceSec1 instSAdeleMeasurableSpaceSec1
  instSIdeleLocallyCompactSec1

local instance : T2Space Iₛ := (sIdeleGroup_description F S).2.1

private theorem sLocalTrace_unit_norm (ξ : Hₛ) : sIdeleNorm F S ξ.val = 1 := by
  obtain ⟨γ, hγ, he⟩ := Subgroup.mem_map.mp ξ.property
  exact he ▸ (sIdeleNorm_spec F S).2 hγ

/-- Auxiliary identity for Theorem 12.4.1.1, Step II, p. 517.
The actual Fourier cutoff followed by dilation and spatial multiplication
can be periodized in its output and paired with the input theta function
through the descended cutoff row. The input measure conversion is
(12.4.1.17), p. 518. -/
theorem sLocalTrace_integral_outputOrbit_cutoff_theta
    (f : BruhatCompactSupport Iₛ) (ρ : Iₛ → ℂ) (σ : Aₛ → ℂ)
    (hσ : Measurable σ) (M : ℝ) (hM : ∀ u, ‖σ u‖ ≤ M)
    (v : testₛ) (x : Iₛ)
    (hcov : ∀ (ξ : Hₛ) (y : Iₛ),
      sLocalTraceCutoffKernel f ρ σ (ξ.val * x) (ξ.val * y).val =
        sLocalTraceCutoffKernel f ρ σ x y.val)
    (κ : Jₛ → ℂ) (hκ : Measurable κ)
    (hrep : ∀ y : Iₛ, κ (QuotientGroup.mk y) =
      ∑' ξ : Hₛ, sLocalTraceCutoffKernel f ρ σ x (ξ.val * y).val)
    (hsum : ∀ y : Iₛ,
      Summable fun ξ : Hₛ ↦ ‖sLocalTraceCutoffKernel f ρ σ x (ξ.val * y).val‖)
    {C : ℝ} (hC : 0 ≤ C)
    (hsmall : ∀ y : Iₛ, normS(y) ≤ 1 →
      (∑' ξ : Hₛ, ‖sLocalTraceCutoffKernel f ρ σ x (ξ.val * y).val‖) ≤
        C * (normS(y)) ^ (-(1 / 4 : ℝ)))
    (hlarge : ∀ y : Iₛ, 1 ≤ normS(y) →
      (∑' ξ : Hₛ, ‖sLocalTraceCutoffKernel f ρ σ x (ξ.val * y).val‖) ≤
        C * (normS(y))⁻¹) :
    let N (q : Jₛ) : ℝ := (sIdeleQuotientNorm F S q).val
    let c : ℂ := sLocalTraceMeasureFactor S
    let G (q : Jₛ) := (N q : ℂ) / c * κ q * sLocalAdelicThetaOnClasses F S v q
    Integrable G μJ ∧
      (∑' ξ : Hₛ, ρ (ξ.val * x) *
        sLocalTraceDilationKernel f (sLocalTraceFourierCutoff σ v) (ξ.val * x).val) =
      ∫ q, G q ∂μJ := by
  intro N c G
  let : BorelSpace Aₛ := sAdeleRing_borelSpace
  let K : Iₛ → Aₛ → ℂ := sLocalTraceCutoffKernel f ρ σ
  have hK (z : Iₛ) : Measurable (K z) :=
    (sLocalTraceCutoffKernel_continuous_additive_row f ρ σ hσ (B := M) hM z).measurable
  obtain ⟨hG, hWeil⟩ := sLocalTrace_integral_outputOrbit_additive_theta
    v K x hK hcov κ hκ hrep hsum hC hsmall hlarge
  refine ⟨hG, ?_⟩
  calc
    _ = ∑' ξ : Hₛ, ∫ y : Aₛ, K (ξ.val * x) y * testAt(v,y) ∂νₛ := by
      apply tsum_congr
      intro ξ
      exact (sLocalTraceCutoffKernel_apply_test f ρ σ hσ M hM v (ξ.val * x)).2.symm
    _ = _ := hWeil

/-- For a Schwartz–Bruhat representative of the Fourier cutoff, the
half-density action of the descended additive row equals spatial
multiplication after quotient Haar convolution by the periodized lift. -/
theorem sLocalTrace_cutoff_halfDensity_quotient_convolution
    (f : BruhatCompactSupport Iₛ) (φ ρ : Jₛ → ℂ)
    (hLift : ∀ g : Iₛ, HasSum (fun ξ : Hₛ ↦ f.val (ξ.val * g)) (φ (QuotientGroup.mk g)))
    (σ : Aₛ → ℂ) (hσ : Measurable σ) (M : ℝ) (hM : ∀ u, ‖σ u‖ ≤ M)
    (v vσ : testₛ) (hcutoff : sLocalTraceFourierCutoff σ v = (fun z : Aₛ ↦ testAt(vσ,z)))
    (x : Iₛ) (κ : Jₛ → ℂ) (hκ : Measurable κ) {C : ℝ} (hC : 0 ≤ C) :
    let ρI : Iₛ → ℂ := ρ ∘ QuotientGroup.mk
    let K : Iₛ → Aₛ → ℂ := sLocalTraceCutoffKernel f ρI σ
    ∀ (hcov : ∀ (ξ : Hₛ) (y : Iₛ), K (ξ.val * x) (ξ.val * y).val = K x y.val)
      (hrep : ∀ y : Iₛ, κ (QuotientGroup.mk y) = ∑' ξ : Hₛ, K x (ξ.val * y).val)
      (hsum : ∀ y : Iₛ, Summable fun ξ : Hₛ ↦ ‖K x (ξ.val * y).val‖)
      (hsmall : ∀ y : Iₛ, normS(y) ≤ 1 →
        (∑' ξ : Hₛ, ‖K x (ξ.val * y).val‖) ≤ C * (normS(y)) ^ (-(1 / 4 : ℝ)))
      (hlarge : ∀ y : Iₛ, 1 ≤ normS(y) →
        (∑' ξ : Hₛ, ‖K x (ξ.val * y).val‖) ≤ C * (normS(y))⁻¹),
      let N (y : Jₛ) : ℝ := (sIdeleQuotientNorm F S y).val
      let q : Jₛ := QuotientGroup.mk x
      let Uσ (y : Jₛ) := (Real.sqrt (N y) : ℂ) * sLocalAdelicThetaOnClasses F S vσ y
      let G (y : Jₛ) := (N y : ℂ) / (sLocalTraceMeasureFactor S : ℂ) * κ y *
        sLocalAdelicThetaOnClasses F S v y
      Integrable G μJ ∧
        (Real.sqrt (N q) : ℂ) * (∫ y, G y ∂μJ) = ρ q * lcaConvolution μJ φ Uσ q := by
  intro ρI K hcov hrep hsum hsmall hlarge N q Uσ G
  obtain ⟨hG, hWeil⟩ := sLocalTrace_integral_outputOrbit_cutoff_theta
    f ρI σ hσ M hM v x hcov κ hκ hrep hsum hC hsmall hlarge
  let m : ℂ := Real.sqrt (N q)
  let d (ξ : Hₛ) := sLocalTraceDilationKernel f (fun z ↦ testAt(vσ,z)) (ξ.val * x).val
  have hρ (ξ : Hₛ) : ρI (ξ.val * x) = ρ q := by
    change ρ (QuotientGroup.mk (ξ.val * x)) = ρ (QuotientGroup.mk x)
    rw [mul_comm ξ.val x, QuotientGroup.mk_mul_of_mem x ξ.property]
  have hraw : (∑' ξ : Hₛ, ρ q * d ξ) = ∫ y, G y ∂μJ := by
    simpa only [hρ, hcutoff, d] using hWeil
  have hD : HasSum (fun ξ : Hₛ ↦ m * d ξ) (lcaConvolution μJ φ Uσ q) :=
    sLocalTraceDilationKernel_periodize_halfDensity f vσ x φ hLift
  refine ⟨hG, ?_⟩
  change m * (∫ y, G y ∂μJ) = _
  calc
    _ = m * ∑' ξ : Hₛ, ρ q * d ξ := congrArg (m * ·) hraw.symm
    _ = ρ q * ∑' ξ : Hₛ, m * d ξ := by simp only [tsum_mul_left]; ring
    _ = _ := congrArg (ρ q * ·) hD.tsum_eq

/-- Moving the input Sobolev density into the row integral and conjugating
the raw periodized action by the half-density gives the normalized kernel. -/
private theorem sLocalTrace_halfDensityKernel_integral
    (s : ℝ) (κ : Jₛ × Jₛ → ℂ) (θ : Jₛ → ℂ) (x : Jₛ)
    (hrow : Integrable (fun y ↦ (((sIdeleQuotientNorm F S y).val : ℝ) : ℂ) /
      (sLocalTraceMeasureFactor S : ℂ) * κ (x, y) * θ y) μJ) :
    let N (y : Jₛ) : ℝ := (sIdeleQuotientNorm F S y).val
    let ℓ := logSIdeleQuotientNorm F S
    let ν := intervalSobolevMeasure μJ ℓ 0 0 s
    let w (y : Jₛ) := intervalSobolevDensity 0 0 s (ℓ y)
    let c : ℂ := sLocalTraceMeasureFactor S
    let U (y : Jₛ) := (Real.sqrt (N y) : ℂ) * θ y
    let K (p : Jₛ × Jₛ) := (Real.sqrt (N p.1 * N p.2) : ℂ) * κ p / (c * (w p.2 : ℂ))
    Integrable (fun y ↦ K (x, y) * U y) ν ∧
      (∫ y, K (x, y) * U y ∂ν) = (Real.sqrt (N x) : ℂ) *
        ∫ y, ((N y : ℂ) / c) * κ (x, y) * θ y ∂μJ := by
  intro N ℓ ν w c U K
  let : BorelSpace Jₛ := ⟨rfl⟩
  let R (y : Jₛ) := ((N y : ℂ) / c) * κ (x, y) * θ y
  have hR : Integrable R μJ := hrow
  have hN₀ (y : Jₛ) : 0 < N y := NNReal.coe_pos.mpr (Units.zero_lt _)
  have hN : Continuous N := NNReal.continuous_coe.comp
    (Units.continuous_val.comp (isProperMap_sIdeleQuotientNorm F S).continuous)
  have hℓ : Continuous ℓ := hN.log fun y ↦ (hN₀ y).ne'
  have hw (y : Jₛ) : 0 < w y := by
    dsimp only [w, intervalSobolevDensity]
    positivity
  have hwm : Measurable w := by
    dsimp only [w, intervalSobolevDensity]
    fun_prop
  have hc : c ≠ 0 := by
    change (sLocalTraceMeasureFactor S : ℂ) ≠ 0
    apply Complex.ofReal_ne_zero.mpr
    unfold sLocalTraceMeasureFactor
    refine ne_of_gt (Finset.prod_pos fun v _ ↦ ?_)
    have hv : 1 < (v.asIdeal.absNorm : ℝ) := by
      exact_mod_cast HeightOneSpectrum.one_lt_absNorm v
    exact div_pos (zero_lt_one.trans hv) (sub_pos.mpr hv)
  let d (y : Jₛ) := ENNReal.ofReal (w y)
  have hdm : Measurable d := hwm.ennreal_ofReal
  have hdf : ∀ᵐ y ∂μJ, d y < ⊤ := ae_of_all _ fun _ ↦ ENNReal.ofReal_lt_top
  have hcancel (y : Jₛ) : (d y).toReal • (K (x, y) * U y) = (Real.sqrt (N x) : ℂ) * R y := by
    have hsquare : (Real.sqrt (N y) : ℂ) ^ 2 = (N y : ℂ) := by
      exact_mod_cast Real.sq_sqrt (hN₀ y).le
    have hwne : (w y : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (hw y).ne'
    dsimp only [d, K, U, R, Prod.fst, Prod.snd]
    rw [ENNReal.toReal_ofReal (hw y).le, Complex.real_smul,
      Real.sqrt_mul (hN₀ x).le, Complex.ofReal_mul, ← hsquare]
    field_simp [hc, hwne] <;> ring
  constructor
  · change Integrable _ ((μJ).withDensity d)
    rw [integrable_withDensity_iff_integrable_smul' hdm hdf]
    exact (hR.const_mul (Real.sqrt (N x) : ℂ)).congr (ae_of_all _ fun y ↦ (hcancel y).symm)
  · change (∫ y, K (x, y) * U y ∂((μJ).withDensity d)) =
      (Real.sqrt (N x) : ℂ) * ∫ y, R y ∂μJ
    rw [integral_withDensity_eq_integral_toReal_smul hdm hdf, ← integral_const_mul]
    exact integral_congr_ae (ae_of_all _ hcancel)

section NormOneConvolutionAverage

set_option quotPrecheck false in
local notation "J₁" => (sIdeleQuotientNorm F S).ker
local notation "ηₛ" => sLocalNormOneQuotientMeasure F S

/-- A fixed preweighted row commutes with the raw character-weighted
norm-one average under a square-root radial bound. Only the fixed row
needs a bound, since the translated rows are obtained by Haar substitution. -/
private theorem sLocalTrace_normOne_integral_kernel_row
    (k : Jₛ × Jₛ → ℂ) (hk : Measurable k) (q : Jₛ)
    (hcov : ∀ (y : Jₛ) (h : J₁), k (q * h.val, y * h.val) = k (q, y))
    (v : Jₛ → ℂ) (hv : Measurable v) (character : PontryaginDual J₁)
    {C : ℝ} (hC : 0 ≤ C)
    (hrow : ∀ y : Jₛ, ‖k (q, y)‖ ≤ C * Real.sqrt ((sIdeleQuotientNorm F S y).val : ℝ))
    (hv₁ : Integrable (fun y : Jₛ ↦ Real.sqrt ((sIdeleQuotientNorm F S y).val : ℝ) * ‖v y‖) μJ) :
    let A (y : Jₛ) := ∫ h : J₁, v (y * h.val) * (character h : ℂ) ∂ηₛ
    let B (h : J₁) := (∫ y : Jₛ, k (q * h.val, y) * v y ∂μJ) * (character h : ℂ)
    Integrable (fun y ↦ k (q, y) * A y) μJ ∧ Integrable B ηₛ ∧
      (∫ y, k (q, y) * A y ∂μJ) = ∫ h, B h ∂ηₛ := by
  intro A B
  let : T2Space Jₛ := instSIdeleQuotientT2Sec1
  let : LocallyCompactSpace Jₛ := instSIdeleQuotientLocallyCompactSec1
  let : SecondCountableTopology Jₛ := instSIdeleQuotientSecondCountableSec1
  let : BorelSpace Jₛ := ⟨rfl⟩
  let : BorelSpace J₁ := ⟨rfl⟩
  let : CompactSpace J₁ := isCompact_iff_compactSpace.mp
    ((isProperMap_sIdeleQuotientNorm F S).isCompact_preimage (isCompact_singleton (x := 1)))
  let : (μJ).IsHaarMeasure := (sLocalQuotientTamagawaMeasure_isWeil (F := F) (S := S)).1
  let : (ηₛ).IsHaarMeasure := (sLocalNormOneQuotientMeasure_normProduct (F := F) (S := S)).1
  let : IsFiniteMeasure ηₛ := CompactSpace.isFiniteMeasure
  let N (y : Jₛ) : ℝ := (sIdeleQuotientNorm F S y).val
  let W (y : Jₛ) := Real.sqrt (N y) * ‖v y‖
  let t (p : J₁ × Jₛ) : Jₛ := p.2 * p.1.val
  have ht : Continuous t := continuous_snd.mul (continuous_subtype_val.comp continuous_fst)
  have hN : Continuous N := NNReal.continuous_coe.comp (Units.continuous_val.comp
    (continuousSIdeleQuotientNorm F S).continuous)
  have hNmul (y : Jₛ) (h : J₁) : N (y * h.val) = N y := by
    change ((sIdeleQuotientNorm F S (y * h.val)).val : ℝ) = _
    rw [map_mul, MonoidHom.mem_ker.mp h.property, mul_one]
  have hW : Integrable W μJ := hv₁
  have hWm : Measurable W := hN.sqrt.measurable.mul hv.norm
  let D (p : J₁ × Jₛ) := C * W (t p)
  have hDm : Measurable D := measurable_const.mul (hWm.comp ht.measurable)
  have hD₀ (p : J₁ × Jₛ) : 0 ≤ D p :=
    mul_nonneg hC (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))
  have hDI : Integrable D ((ηₛ).prod μJ) := by
    refine (integrable_prod_iff hDm.aestronglyMeasurable).2 ⟨ae_of_all _ fun h ↦ ?_, ?_⟩
    · exact (measurePreserving_mul_right μJ h.val).integrable_comp_of_integrable (hW.const_mul C)
    · have hnorm (h : J₁) : (∫ y, ‖D (h, y)‖ ∂μJ) = ∫ y, C * W y ∂μJ := by
        have hn (y : Jₛ) : ‖D (h, y)‖ = C * W (y * h.val) := Real.norm_of_nonneg (hD₀ (h, y))
        simp_rw [hn]
        exact integral_mul_right_eq_self (fun y ↦ C * W y) h.val
      simp_rw [hnorm]
      exact integrable_const _
  let H (h : J₁) (y : Jₛ) := k (q, y) * v (y * h.val) * (character h : ℂ)
  have hkq : Measurable (fun y : Jₛ ↦ k (q, y)) := hk.comp (measurable_const.prodMk measurable_id)
  have hcharacter : Continuous (fun h : J₁ ↦ (character h : ℂ)) := continuous_subtype_val.comp character.continuous_toFun
  have hHm : Measurable (Function.uncurry H) :=
    ((hkq.comp measurable_snd).mul (hv.comp ht.measurable)).mul (hcharacter.measurable.comp measurable_fst)
  have hHI : Integrable (Function.uncurry H) ((ηₛ).prod μJ) := by
    refine hDI.mono' hHm.aestronglyMeasurable (ae_of_all _ fun p ↦ ?_)
    rcases p with ⟨h, y⟩
    dsimp only [Function.uncurry, H, D, t, W, Prod.fst, Prod.snd]
    rw [norm_mul, norm_mul, Circle.norm_coe, mul_one, hNmul, ← mul_assoc]
    exact mul_le_mul_of_nonneg_right (hrow y) (norm_nonneg _)
  have hy (y : Jₛ) : (∫ h, H h y ∂ηₛ) = k (q, y) * A y := by
    simp only [H, A, mul_assoc, integral_const_mul]
  have hh (h : J₁) : (∫ y, H h y ∂μJ) = B h := by
    let L (y : Jₛ) := k (q * h.val, y) * v y * (character h : ℂ)
    calc
      _ = ∫ y, L (y * h.val) ∂μJ := integral_congr_ae (ae_of_all _ fun y ↦ by
        simp only [H, L, hcov])
      _ = ∫ y, L y ∂μJ := integral_mul_right_eq_self L h.val
      _ = B h := by simp only [L, B, integral_mul_const]
  refine ⟨hHI.integral_prod_right.congr (ae_of_all _ hy),
    hHI.integral_prod_left.congr (ae_of_all _ hh), ?_⟩
  calc
    _ = ∫ y, ∫ h, H h y ∂ηₛ ∂μJ := integral_congr_ae (ae_of_all _ fun y ↦ (hy y).symm)
    _ = ∫ h, ∫ y, H h y ∂μJ ∂ηₛ := (integral_integral_swap hHI).symm
    _ = _ := integral_congr_ae (ae_of_all _ hh)

/-- The ordinary theta representative satisfies the square-root-weighted
quotient L¹ hypothesis of the row interchange. -/
private theorem sLocalTrace_theta_sqrt_norm_integrable (v : testₛ) :
    Integrable (fun y : Jₛ ↦ Real.sqrt ((sIdeleQuotientNorm F S y).val : ℝ) *
      ‖sLocalAdelicThetaOnClasses F S v y‖) μJ := by
  let circleToComplex : Circle →ₜ* ℂ := ⟨Circle.coeHom, continuous_subtype_val⟩
  let c := quasiCharacterNormTwist (sIdeleQuotientNorm F S)
    (isProperMap_sIdeleQuotientNorm F S).continuous
    (circleToComplex.comp (1 : PontryaginDual Jₛ)) (1 / 2)
  have h := sLocalThetaMellinIntegral_integrable v c ⟨1, 1 / 2, by norm_num, rfl⟩
  have hc (y : Jₛ) : ‖c y‖ = Real.sqrt ((sIdeleQuotientNorm F S y).val : ℝ) := by
    change ‖((1 : PontryaginDual Jₛ) y : ℂ) *
      (((sIdeleQuotientNorm F S y).val : ℝ) : ℂ) ^ (1 / 2 : ℂ)‖ = _
    rw [norm_mul, Circle.norm_coe, one_mul,
      Complex.norm_cpow_eq_rpow_re_of_pos (NNReal.coe_pos.mpr (Units.zero_lt _)),
      Real.sqrt_eq_rpow] <;> norm_num
  refine h.norm.congr (ae_of_all _ fun y ↦ ?_)
  change ‖sLocalAdelicThetaOnClasses F S v y * c y‖ = _
  rw [norm_mul, hc, mul_comm]

/-- The fixed weighted cutoff row acts on homogeneous theta tests by quotient
Haar convolution of the homogeneous cutoff output, followed by the spatial
multiplier. Both homogeneous theta functions use the raw norm-one Tamagawa
average. -/
theorem sLocalTrace_normOne_cutoff_weighted_quotient_convolution
    (s : ℝ) (φ : C(Jₛ, ℂ)) (hφ : HasCompactSupport (φ : Jₛ → ℂ))
    (ρ : Jₛ → ℂ) (hρ : ∀ (z : Jₛ) (h : J₁), ρ (z * h.val) = ρ z)
    (κ : Jₛ × Jₛ → ℂ) (hκ : Measurable κ) (q : Jₛ)
    (hcov : ∀ (y : Jₛ) (h : J₁), κ (q * h.val, y * h.val) = κ (q, y))
    (v vσ : testₛ) (character : PontryaginDual J₁) {C : ℝ} (hC : 0 ≤ C) :
    let N (y : Jₛ) : ℝ := (sIdeleQuotientNorm F S y).val
    let c : ℂ := sLocalTraceMeasureFactor S
    let k (p : Jₛ × Jₛ) := (N p.2 : ℂ) / c * κ p
    let θ := sLocalAdelicThetaOnClasses F S v
    let Uσ (y : Jₛ) := (Real.sqrt (N y) : ℂ) * sLocalAdelicThetaOnClasses F S vσ y
    ∀ (hrow : ∀ y : Jₛ, ‖k (q, y)‖ ≤ C * Real.sqrt (N y))
      (hplain : ∀ h : J₁, (Real.sqrt (N (q * h.val)) : ℂ) *
        (∫ y, k (q * h.val, y) * θ y ∂μJ) =
          ρ (q * h.val) * lcaConvolution μJ φ Uσ (q * h.val)),
      let Ucharacter (y : Jₛ) := (Real.sqrt (N y) : ℂ) * sLocalHomogeneousAdelicThetaLinearMap F S character v y
      let UcutoffCharacter (y : Jₛ) := (Real.sqrt (N y) : ℂ) * sLocalHomogeneousAdelicThetaLinearMap F S character vσ y
      let ℓ := logSIdeleQuotientNorm F S
      let ν := intervalSobolevMeasure μJ ℓ 0 0 s
      let row (y : Jₛ) := (Real.sqrt (N q * N y) : ℂ) * κ (q, y) /
        (c * (intervalSobolevDensity 0 0 s (ℓ y) : ℂ))
      Integrable (fun y ↦ row y * Ucharacter y) ν ∧
        (∫ y, row y * Ucharacter y ∂ν) = ρ q * lcaConvolution μJ φ UcutoffCharacter q := by
  intro N c k θ Uσ hrow hplain Ucharacter UcutoffCharacter ℓ ν row
  let : BorelSpace Jₛ := ⟨rfl⟩
  have hN : Continuous N := NNReal.continuous_coe.comp (Units.continuous_val.comp
    (continuousSIdeleQuotientNorm F S).continuous)
  have hNmul (y : Jₛ) (h : J₁) : N (y * h.val) = N y := by
    change ((sIdeleQuotientNorm F S (y * h.val)).val : ℝ) = _
    rw [map_mul, MonoidHom.mem_ker.mp h.property, mul_one]
  have hk : Measurable k :=
    (((Complex.continuous_ofReal.comp hN).measurable.comp measurable_snd).div measurable_const).mul hκ
  have hkc (y : Jₛ) (h : J₁) : k (q * h.val, y * h.val) = k (q, y) := by
    simp only [k, hNmul, hcov]
  obtain ⟨hInt, _, hIntertwine⟩ := sLocalTrace_normOne_integral_kernel_row
    k hk q hkc θ θ.continuous.measurable character hC hrow
    (sLocalTrace_theta_sqrt_norm_integrable v)
  let thetaCharacter := sLocalHomogeneousAdelicThetaLinearMap F S character v
  have hIntω : Integrable (fun y ↦ k (q, y) * thetaCharacter y) μJ := by
    simpa only [thetaCharacter, sLocalHomogeneousAdelicThetaLinearMap_apply] using hInt
  have hIntertwineω : (∫ y, k (q, y) * thetaCharacter y ∂μJ) =
      ∫ h : J₁, (∫ y, k (q * h.val, y) * θ y ∂μJ) * (character h : ℂ) ∂ηₛ := by
    simpa only [thetaCharacter, sLocalHomogeneousAdelicThetaLinearMap_apply] using hIntertwine
  obtain ⟨hWeighted, hDensity⟩ := sLocalTrace_halfDensityKernel_integral s κ thetaCharacter q hIntω
  let uσ : C(Jₛ, ℂ) := ⟨Uσ, (Complex.continuous_ofReal.comp hN.sqrt).mul
    (sLocalAdelicThetaOnClasses F S vσ).continuous⟩
  have hAvg (y : Jₛ) : (∫ h : J₁, uσ (y * h.val) * (character h : ℂ) ∂ηₛ) = UcutoffCharacter y := by
    change (∫ h : J₁, Uσ (y * h.val) * (character h : ℂ) ∂ηₛ) = UcutoffCharacter y
    simp only [Uσ, UcutoffCharacter, hNmul, mul_assoc, integral_const_mul,
      sLocalHomogeneousAdelicThetaLinearMap_apply]
  refine ⟨hWeighted, hDensity.trans ?_⟩
  calc
    _ = (Real.sqrt (N q) : ℂ) *
        ∫ h : J₁, (∫ y, k (q * h.val, y) * θ y ∂μJ) * (character h : ℂ) ∂ηₛ :=
      congrArg ((Real.sqrt (N q) : ℂ) * ·) hIntertwineω
    _ = ∫ h : J₁, ρ (q * h.val) * lcaConvolution μJ φ uσ (q * h.val) * (character h : ℂ) ∂ηₛ := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      exact ae_of_all _ fun h ↦ by
        change (Real.sqrt (N q) : ℂ) *
            ((∫ y, k (q * h.val, y) * θ y ∂μJ) * (character h : ℂ)) =
          ρ (q * h.val) * lcaConvolution μJ φ Uσ (q * h.val) * (character h : ℂ)
        rw [← mul_assoc]
        exact congrArg (· * (character h : ℂ)) (by simpa only [hNmul] using hplain h)
    _ = ρ q * lcaConvolution μJ φ
        (fun y ↦ ∫ h : J₁, uσ (y * h.val) * (character h : ℂ) ∂ηₛ) q :=
      sLocalTrace_normOne_integral_mul_convolution φ uσ hφ ρ hρ character q
    _ = _ := by simp_rw [hAvg]

private theorem sLocalTrace_mul_absOrbit_le_sqrt {t A C : ℝ} (ht : 0 < t) (hC : 0 ≤ C)
    (hsmall : t ≤ 1 → A ≤ C * t ^ (-(1 / 4 : ℝ)))
    (hlarge : 1 ≤ t → A ≤ C * t⁻¹) : t * A ≤ C * Real.sqrt t := by
  rw [Real.sqrt_eq_rpow]
  rcases le_total t 1 with hs | hl
  · calc
      t * A ≤ t * (C * t ^ (-(1 / 4 : ℝ))) := mul_le_mul_of_nonneg_left (hsmall hs) ht.le
      _ = C * (t ^ (1 : ℝ) * t ^ (-(1 / 4 : ℝ))) := by rw [Real.rpow_one]; ring
      _ = C * t ^ (3 / 4 : ℝ) := by rw [← Real.rpow_add ht]; norm_num
      _ ≤ _ := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_ge ht hs (by norm_num)) hC
  · calc
      t * A ≤ t * (C * t⁻¹) := mul_le_mul_of_nonneg_left (hlarge hl) ht.le
      _ = C * t ^ (0 : ℝ) := by rw [Real.rpow_zero, mul_left_comm, mul_inv_cancel₀ ht.ne', mul_one]
      _ ≤ _ := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hl (by norm_num)) hC

/-- Assemble the homogeneous weighted row identity from the absolute orbit
bounds and the covariance of the actual additive cutoff kernel. -/
theorem sLocalTrace_cutoff_weighted_homogeneous_of_orbit_data
    (s : ℝ) (f : BruhatCompactSupport Iₛ) (φ : C(Jₛ, ℂ))
    (hφ : HasCompactSupport (φ : Jₛ → ℂ))
    (hLift : ∀ g : Iₛ, HasSum (fun ξ : Hₛ ↦ f.val (ξ.val * g)) (φ (QuotientGroup.mk g)))
    (ρ : Jₛ → ℂ) (hρ : ∀ (q : Jₛ) (h : J₁), ρ (q * h.val) = ρ q)
    (σ : Aₛ → ℂ) (hσ : Measurable σ) (M : ℝ) (hM : ∀ u, ‖σ u‖ ≤ M)
    (v vσ : testₛ) (hcutoff : sLocalTraceFourierCutoff σ v = (fun z : Aₛ ↦ testAt(vσ,z)))
    (κ : Jₛ → Jₛ → ℂ) (hκ : Measurable (fun p : Jₛ × Jₛ ↦ κ p.1 p.2))
    (hQCov : ∀ (q y : Jₛ) (h : J₁), κ (q * h.val) (y * h.val) = κ q y)
    {C : ℝ} (hC : 0 ≤ C) (q : Jₛ) (character : PontryaginDual J₁) :
    let ρI : Iₛ → ℂ := ρ ∘ QuotientGroup.mk
    let K : Iₛ → Aₛ → ℂ := sLocalTraceCutoffKernel f ρI σ
    ∀ (_hRawCov : ∀ (ξ : Hₛ) (x y : Iₛ), K (ξ.val * x) (ξ.val * y).val = K x y.val)
      (_hRep : ∀ x y : Iₛ, κ (QuotientGroup.mk x) (QuotientGroup.mk y) =
        ∑' ξ : Hₛ, K x (ξ.val * y).val)
      (_hAbs : ∀ x y : Iₛ,
        let A := ∑' ξ : Hₛ, ‖K x (ξ.val * y).val‖
        Summable (fun ξ : Hₛ ↦ ‖K x (ξ.val * y).val‖) ∧
          (normS(y) ≤ 1 → A ≤ C * (normS(y)) ^ (-(1 / 4 : ℝ))) ∧
          (1 ≤ normS(y) → A ≤ C * (normS(y))⁻¹)),
      let N (p : Jₛ) : ℝ := (sIdeleQuotientNorm F S p).val
      let c : ℂ := sLocalTraceMeasureFactor S
      let U (y : Jₛ) := (Real.sqrt (N y) : ℂ) *
        sLocalHomogeneousAdelicThetaLinearMap F S character v y
      let Uσ (y : Jₛ) := (Real.sqrt (N y) : ℂ) *
        sLocalHomogeneousAdelicThetaLinearMap F S character vσ y
      let ℓ := logSIdeleQuotientNorm F S
      let ν := intervalSobolevMeasure μJ ℓ 0 0 s
      let row (y : Jₛ) := (Real.sqrt (N q * N y) : ℂ) * κ q y /
        (c * (intervalSobolevDensity 0 0 s (ℓ y) : ℂ))
      Integrable (fun y ↦ row y * U y) ν ∧
        (∫ y, row y * U y ∂ν) = ρ q * lcaConvolution μJ φ Uσ q := by
  intro ρI K hRawCov hRep hAbs N c U Uσ ℓ ν row
  let k (p y : Jₛ) := (N y : ℂ) / c * κ p y
  let θ := sLocalAdelicThetaOnClasses F S v
  let Vσ (y : Jₛ) := (Real.sqrt (N y) : ℂ) * sLocalAdelicThetaOnClasses F S vσ y
  have hClass (p : Jₛ) : (QuotientGroup.mk p.out : Jₛ) = p := QuotientGroup.out_eq' p
  have hNorm (p : Jₛ) : normS(p.out) = N p := by
    dsimp only [N]
    rw [← sIdeleQuotientNorm_mk, hClass]
  have hκrow (p : Jₛ) : Measurable (κ p) := hκ.comp (measurable_const.prodMk measurable_id)
  have hPlain (p : Jₛ) : (Real.sqrt (N p) : ℂ) * (∫ y, k p y * θ y ∂μJ) =
      ρ p * lcaConvolution μJ φ Vσ p := by
    let x : Iₛ := p.out
    have hx : (QuotientGroup.mk x : Jₛ) = p := hClass p
    have hxRep (y : Iₛ) : κ p (QuotientGroup.mk y) = ∑' ξ : Hₛ, K x (ξ.val * y).val := by
      simpa only [hx] using hRep x y
    have h := sLocalTrace_cutoff_halfDensity_quotient_convolution
      f φ ρ hLift σ hσ M hM v vσ hcutoff x (κ p) (hκrow p) hC
      (fun ξ y ↦ hRawCov ξ x y) hxRep (fun y ↦ (hAbs x y).1)
      (fun y ↦ (hAbs x y).2.1) (fun y ↦ (hAbs x y).2.2)
    simpa only [hx, N, c, k, θ, Vσ] using h.2
  have hBound (y : Jₛ) : ‖k q y‖ ≤ (C / ‖c‖) * Real.sqrt (N y) := by
    let A := ∑' ξ : Hₛ, ‖K q.out (ξ.val * y.out).val‖
    have hκA : ‖κ q y‖ ≤ A := by
      have hr : κ q y = ∑' ξ : Hₛ, K q.out (ξ.val * y.out).val := by
        simpa only [hClass] using hRep q.out y.out
      rw [hr]
      exact norm_tsum_le_tsum_norm (hAbs q.out y.out).1
    have hy : 0 < N y := NNReal.coe_pos.mpr (Units.zero_lt _)
    have hA : N y * A ≤ C * Real.sqrt (N y) := by
      apply sLocalTrace_mul_absOrbit_le_sqrt hy hC
      · intro ht
        have ht' : normS(y.out) ≤ 1 := by rwa [hNorm]
        simpa only [A, hNorm] using (hAbs q.out y.out).2.1 ht'
      · intro ht
        have ht' : 1 ≤ normS(y.out) := by rwa [hNorm]
        simpa only [A, hNorm] using (hAbs q.out y.out).2.2 ht'
    calc
      ‖k q y‖ = N y * ‖κ q y‖ / ‖c‖ := by
        dsimp only [k]
        rw [norm_mul, norm_div, Complex.norm_real, Real.norm_of_nonneg hy.le]
        ring
      _ ≤ (C * Real.sqrt (N y)) / ‖c‖ := div_le_div_of_nonneg_right
        ((mul_le_mul_of_nonneg_left hκA hy.le).trans hA) (norm_nonneg _)
      _ = _ := by ring
  exact sLocalTrace_normOne_cutoff_weighted_quotient_convolution s φ hφ ρ hρ
    (fun p ↦ κ p.1 p.2) hκ q (hQCov q) v vσ character
    (div_nonneg hC (norm_nonneg c)) hBound (fun h ↦ hPlain (q * h.val))


end NormOneConvolutionAverage

local notation "A" => Aₛ
local notation "I" => Iₛ
local notation "H" => Hₛ
local notation "J" => Jₛ
local notation "Q" => continuousSIdeleQuotientNorm F S
local notation "M(" z ")" => ((∏ w : InfinitePlace F, ‖(z : A).1 w‖ ^ InfinitePlace.mult w) *
  ∏ v : S, ‖(z : A).2 v‖)


/-- With a realized input cutoff, the uncompressed fixed-annulus row is
quotient convolution of the cutoff output followed by spatial multiplication.
A homogeneous quotient test makes every other character row vanish. -/
theorem exists_sLocalTrace_fixedAnnulus_realizedCutoff_kernel_rows
    (f : BruhatCompactSupport I) (φ : C(J, ℂ)) (hφ : HasCompactSupport (φ : J → ℂ))
    (hLift : ∀ g : I, HasSum (fun ξ : H ↦ f.val (ξ.val * g)) (φ (QuotientGroup.mk g)))
    (b : ℝ → ℂ) {Λ ερ εb Cb s : ℝ} {ρ : J → ℝ}
    (hρ : IsModulatedCutoff Q Λ ερ ρ) (hs : 0 ≤ s)
    (hb : ContDiff ℝ (2 * (((∑ w : InfinitePlace F, w.mult) + Fintype.card S) + 1) : ℕ) b)
    (hε : 0 < εb) (hplateau : EqOn b (fun _ ↦ b 0) (Icc 0 εb))
    (hderiv : ∀ j ≤ 2 * (((∑ w : InfinitePlace F, w.mult) + Fintype.card S) + 1),
      ∀ r, 0 ≤ r → ‖iteratedDeriv j b r‖ ≤ Cb) :
    let N (q : J) : ℝ := (Q q).val
    let μ := sLocalQuotientTamagawaMeasure F S
    let ℓ := logSIdeleQuotientNorm F S
    let ν := intervalSobolevMeasure μ ℓ 0 0 s
    ∃ κ : J → J → ℂ,
      (∀ x y : I, κ (QuotientGroup.mk x) (QuotientGroup.mk y) =
        ∑' ξ : H, sLocalTraceCutoffKernel f (fun a ↦ (ρ (QuotientGroup.mk a) : ℂ))
          (fun v ↦ b (M(v))) x (ξ.val * y).val) ∧
      let K (p : J × J) := (Real.sqrt (N p.1 * N p.2) : ℂ) * κ p.1 p.2 /
        ((sLocalTraceMeasureFactor S : ℂ) * (intervalSobolevDensity 0 0 s (ℓ p.2) : ℂ))
      MemLp K 2 (ν.prod ν) ∧
      ∀ (v vσ : SchwartzBruhat (Multiplicative A)),
        sLocalTraceFourierCutoff (fun z : A ↦ b (M(z))) v =
          (fun z : A ↦ vσ (Multiplicative.ofAdd z)) →
        ∀ (character : PontryaginDual (sIdeleQuotientNorm F S).ker) (q : J),
          let U (y : J) := (Real.sqrt (N y) : ℂ) *
            sLocalHomogeneousAdelicThetaLinearMap F S character v y
          let V (y : J) := (Real.sqrt (N y) : ℂ) *
            sLocalHomogeneousAdelicThetaLinearMap F S character vσ y
          Integrable (fun y ↦ K (q, y) * U y) ν ∧
            (∫ y, K (q, y) * U y ∂ν) = (ρ q : ℂ) * lcaConvolution μ φ V q ∧
            ∀ target : PontryaginDual (sIdeleQuotientNorm F S).ker, target ≠ character →
              (∀ (y : J) (h : (sIdeleQuotientNorm F S).ker),
                φ (y * h.val) = (target h : ℂ)⁻¹ * φ y) →
              (∫ y, K (q, y) * U y ∂ν) = 0 := by
  intro N μ ℓ ν
  obtain ⟨_, κ, C, hC, hκ, _, hRep, hRaw, hQCov, hAbs, hK⟩ :=
    exists_sLocalTrace_halfDensityOrbitKernel_fixed_annulus_data f b hρ hs hb hε hplateau hderiv
  refine ⟨κ, hRep, hK, ?_⟩
  intro v vσ hcutoff character q
  let : BorelSpace A := sAdeleRing_borelSpace
  have hmod : Continuous (fun z : A ↦ M(z)) :=
    (continuous_finsetProd _ fun w _ ↦ ((continuous_apply w).comp continuous_fst).norm.pow _).mul
    (continuous_finsetProd _ fun p _ ↦ ((continuous_apply p).comp continuous_snd).norm)
  have hmod₀ (z : A) : 0 ≤ M(z) := by positivity
  have hBound (z : A) : ‖b (M(z))‖ ≤ Cb := by
    simpa only [iteratedDeriv_zero] using hderiv 0 (Nat.zero_le _) (M(z)) (hmod₀ z)
  obtain ⟨profile, _, hprofile, _⟩ := hρ.profile
  have hρInv (p : J) (h : (sIdeleQuotientNorm F S).ker) :
      (ρ (p * h.val) : ℂ) = (ρ p : ℂ) := by
    apply congrArg Complex.ofReal
    rw [hprofile, hprofile]
    change profile (((Q (p * h.val)).val : ℝ)) = profile (((Q p).val : ℝ))
    rw [map_mul, show Q h.val = 1 from MonoidHom.mem_ker.mp h.property, mul_one]
  have hRows := sLocalTrace_cutoff_weighted_homogeneous_of_orbit_data s f φ hφ hLift
    (fun p ↦ (ρ p : ℂ)) hρInv (fun z : A ↦ b (M(z))) (hb.continuous.comp hmod).measurable
    Cb hBound v vσ hcutoff κ hκ hQCov hC q character
    (fun ξ x y ↦ hRaw ξ.val (sLocalTrace_unit_norm (F := F) (S := S) ξ) x y) hRep hAbs
  refine ⟨hRows.1, hRows.2, ?_⟩
  intro target hne hHom
  have hZero := sLocalTrace_lcaConvolution_halfDensityTheta_eq_zero_of_ne_normOne
    (F := F) (S := S) φ target character hne hHom vσ q
  exact hRows.2.trans (mul_eq_zero_of_right _ hZero)

end RiemannMasullo
