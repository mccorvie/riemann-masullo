module

import Mathlib.Geometry.Manifold.PartitionOfUnity
import RiemannMasullo.Ch10_TraceSpectral.Sec4b_ProjectedKernels
public import RiemannMasullo.Ch12_TraceGeometric.Sec5

public import RiemannMasullo.ForMathlib.Analysis.Fourier.QuadraticBoxProfile
public import RiemannMasullo.ForMathlib.NumberTheory.NumberField.GaussianPlaces
import RiemannMasullo.Ch03_IdelicZeta.PrincipalAngularCharacter
import RiemannMasullo.Ch05_ThetaZSpaces.Sec2b_IsotypicAverages
import RiemannMasullo.Ch06_LocalGlobal.Sec3
import RiemannMasullo.AppB_AnalyticNT.Sec4b
import Mathlib.Analysis.Calculus.ContDiff.Convolution

/-! # Isolated statements of §12.5

The projective strip kernel and its consequences for the smoothened geometric diagonal.

## The projective strip kernel needed for (12.5.1.4)

The first theorem supplies the kernel hypothesis of the smoothened diagonal formula in §12.5.
The second theorem specializes that formula to this kernel.
-/

@[expose] public noncomputable section

open MeasureTheory NumberField Set
open scoped NNReal

namespace RiemannMasullo.Isolated

set_option quotPrecheck false

attribute [local instance] instIdeleClassMeasurableSpaceSec1 instIdeleClassBorelSpaceSec1
  instIdeleClassT2Sec1 instIdeleClassLocallyCompactSec1 instIdeleClassSecondCountableSec1
  instIdeleClassHaarMeasureSec1

variable {F : Type*} [Field F] [NumberField F]

local notation "C𝔽" => IdeleClassGroup (𝓞 F) F
local notation "C₁" => (ideleClassNorm F).ker
local notation "μ𝔽" => ideleClassTamagawaMeasure F
local notation "m𝔽" => (continuousIdeleClassNorm F : C𝔽 →ₜ* ℝ≥0ˣ)
local notation "hs₁(" hs ")" => (lt_of_lt_of_le (by norm_num : (1 : ℝ) < 3) hs)
local notation "hs₀(" hs ")" => (zero_lt_one.trans hs₁(hs)).le

/-- Paper: (12.5.1.4), p. 520. For a test vanishing on the norm-one classes, a projective
Sobolev tensor represents convolution by the test after spectral projection at twist 1/2.
Reconstruction: Definition 10.4.3.7(2), p. 473, subtracts the spectral kernel. Using this
subtraction on p. 520 presupposes a tensor for the operator in (10.4.3.45).
Deviation: We ask for any representing tensor, restricted to the positive half-widths and
tests of Theorem 12.5.1.1. We impose no finite-rank expansion on the tensor.
Quotient nuclearity and a finite decomposition into weighted adjoints give the representing
tensor. The paper uses it on pp. 520, 522. -/
theorem exists_projectiveKernel_stripTestAction_spectralProjection
    (φ : BruhatCompactSupport C𝔽) (_hφ : ∀ g : C₁, φ.val g = 0)
    {α s : ℝ} (hα : 0 < α) (hs : 3 ≤ s) :
    ∃ K, sobolevProjectiveKernelOperator (F := F) hα.le hs₀(hs) K =
      (hardySobolevTestAction μ𝔽 m𝔽 (-α) α s ((neg_nonpos.mpr hα.le).trans hα.le) hs₀(hs) φ).comp
        (spectralProjection (F := F) (1 / 2) hα.le hs₀(hs)) := by
  exact stripTestAction_spectralProjection_has_projectiveKernel (1 / 2) hα.le hs₀(hs) φ

/-- Paper: (12.5.1.4), p. 520. The smoothened geometric diagonal is Haar-integrable, and the
strip zero terms sum absolutely to its negative integral.
Deviation: As in §12.5 of the library, a measurable D′-sequence specifies the smoothening,
and the sum uses the closed strip with strict reciprocal-weight multiplicities on its edges.
It agrees with the printed interior sum when both edges are zero-free.
The projective kernel above supplies the witness in the smoothened diagonal formula. -/
theorem hasSum_stripZeros_neg_integral_smoothenedDiagonal_of_vanishing
    (φ : BruhatCompactSupport C𝔽) (hφ : ∀ g : C₁, φ.val g = 0)
    (χ : PontryaginDual C₁ → PontryaginDual C𝔽) (hχ : IsSpectralBasepointChoice χ)
    {α s : ℝ} (hα : 0 < α) (hs : 3 ≤ s)
    (U : ℕ → Set C𝔽) (hU : IsDPrimeSequence μ𝔽 U) (hBorel : ∀ n, MeasurableSet (U n)) :
    let hK := exists_projectiveKernel_stripTestAction_spectralProjection φ hφ hα hs
    let diagonal (x : C𝔽) := dSequenceKernelSmoothening μ𝔽 U
      (globalStripGeometricKernel (F := F) (1 / 2) hα.le hs₁(hs) φ hK) (x, x)
    let shift (b t : ℝ) := (b : ℂ) + (t : ℂ) * Complex.I
    let order (η : PontryaginDual C𝔽) := meromorphicOrderAt (continuedCompletedHeckeL η)
    let Z := {z : PontryaginDual C₁ × ℝ × ℝ //
      z.2.1 ∈ Icc (-α) α ∧ 0 < order (χ z.1) (shift (1 / 2 + z.2.1) z.2.2)}
    let term (z : Z) := ((spectralStripMultiplicity α s z.val.2.1
      (order (χ z.val.1) (shift (1 / 2 + z.val.2.1) z.val.2.2)).untop₀.toNat : ℕ) : ℂ) *
      modulatedFourierMellin m𝔽 univ ⟨isProperMap_ideleClassNorm F, ideleClassNorm_ne_one (F := F)⟩
        μ𝔽 φ.val (ideleClassNormTwist (χ z.val.1) (shift z.val.2.1 z.val.2.2))
    Integrable diagonal μ𝔽 ∧ Summable (fun z ↦ ‖term z‖) ∧
      HasSum term (-(∫ x, diagonal x ∂μ𝔽)) :=
  hasSum_stripZeros_neg_integral_smoothenedDiagonal φ hφ χ hχ hα hs
    (exists_projectiveKernel_stripTestAction_spectralProjection φ hφ hα hs) U hU hBorel

/-! ## Localizing the kernel condition

Tests supported in any prescribed nonempty open set of log norms suffice to check the kernel condition.
-/

section KernelLocalization

open scoped ContDiff

local notation "ℓ" => logIdeleClassNorm F
local notation "W(" α ", " s ")" => CompactIntervalSobolev μ𝔽 ℓ (-α) α s
local notation "A(" ha ", " hs ", " φ ")" =>
  hardySobolevTestAction μ𝔽 m𝔽 _ _ _ ((neg_nonpos.mpr ha).trans ha) hs φ
local notation "T(" ha ", " hs ", " g ")" =>
  hardySobolevTranslation μ𝔽 m𝔽 _ _ _ ((neg_nonpos.mpr ha).trans ha) hs g
local notation "kerExists(" ha ", " hs ", " P ", " φ ")" =>
  (∃ K, sobolevProjectiveKernelOperator (F := F) ha hs K = (A(ha, hs, φ)).comp P)

private theorem kernelLocalization_exists_translate (g : C𝔽) (φ : BruhatCompactSupport C𝔽) :
    ∃ ψ : BruhatCompactSupport C𝔽, ∀ x, ψ.val x = φ.val (g⁻¹ * x) := by
  have hφ := modulationWeight_mem_schwartzBruhat m𝔽 univ ⟨0, mem_univ _⟩
    ⟨φ.val, bruhatCompactSupport_le_modulatedExponentialDecay m𝔽 univ
      ⟨isProperMap_ideleClassNorm F, ideleClassNorm_ne_one (F := F)⟩
      (fun t ↦ ⟨QuotientGroup.mk (canonicalIdeleNormSection F t),
        canonicalIdeleNormSection_rightInverse F t⟩) φ.property⟩
  rw [modulationWeight_zero] at hφ
  let f : SchwartzBruhat C𝔽 := ⟨φ.val, hφ⟩
  have hsm := schwartzBruhat_isBruhatSmooth (schwartzBruhatTranslate g f)
  have hc := (show HasCompactSupport φ.val from φ.property.2).comp_homeomorph
    (Homeomorph.mulLeft g⁻¹)
  exact ⟨⟨_, (mem_bruhatSmoothSubmodule_iff _).mpr hsm, hc⟩, fun _ ↦ rfl⟩

/-- Left translating a test postcomposes its weighted strip convolution with the same
translation. -/
theorem stripTestAction_translate {α s : ℝ} (ha : 0 ≤ α) (hs : 0 ≤ s)
    (g : C𝔽) (φ ψ : BruhatCompactSupport C𝔽) (hψ : ∀ x, ψ.val x = φ.val (g⁻¹ * x)) :
    A(ha, hs, ψ) = (T(ha, hs, g)).comp (A(ha, hs, φ)) := by
  apply ContinuousLinearMap.ext
  intro u
  apply Lp.ext
  apply (withDensity_absolutelyContinuous μ𝔽 _).ae_eq
  have hφ := hardySobolevTestAction_apply μ𝔽 m𝔽 _ _ _ ((neg_nonpos.mpr ha).trans ha) hs φ u
  have htr := (measurePreserving_mul_left μ𝔽 g⁻¹).quasiMeasurePreserving.ae_eq_comp hφ
  have ht := hardySobolevTranslation_apply μ𝔽 m𝔽 _ _ _ ((neg_nonpos.mpr ha).trans ha) hs g
    (A(ha, hs, φ) u)
  filter_upwards [hardySobolevTestAction_apply μ𝔽 m𝔽 _ _ _ ((neg_nonpos.mpr ha).trans ha) hs ψ u,
    htr, ht] with x hx hy hz
  refine hx.trans ((?_ : lcaConvolution μ𝔽 ψ.val u x =
    lcaConvolution μ𝔽 φ.val u (g⁻¹ * x)).trans (hy.symm.trans hz.symm))
  unfold lcaConvolution
  rw [← integral_mul_left_eq_self (fun y ↦ ψ.val y * u (y⁻¹ * x)) g]
  apply integral_congr_ae (.of_forall fun y ↦ ?_)
  rw [hψ, inv_mul_cancel_left, mul_inv_rev, mul_assoc]

private theorem kernelLocalization_nuclear_iff {α s : ℝ} (ha : 0 ≤ α) (hs : 0 ≤ s)
    (B : W(α, s) →L[ℂ] W(α, s)) :
    (∃ K, sobolevProjectiveKernelOperator (F := F) ha hs K = B) ↔ IsNuclearOperator B := by
  refine ⟨fun ⟨K, hK⟩ ↦ (existsUnique_sobolevProjectiveKernel_iff_nuclear ha hs B).mp
    ⟨K, hK, fun L hL ↦ sobolevProjectiveKernelOperator_injective ha hs (hL.trans hK.symm)⟩,
    fun h ↦ ((existsUnique_sobolevProjectiveKernel_iff_nuclear ha hs B).mpr h).exists⟩

/-- Translating a test preserves projective kernel existence after any fixed input
operator on the strip. The inverse translation gives the converse. -/
theorem stripTestAction_projectiveKernel_translate_iff {α s : ℝ} (ha : 0 ≤ α) (hs : 0 ≤ s)
    (P : W(α, s) →L[ℂ] W(α, s)) (g : C𝔽) (φ ψ : BruhatCompactSupport C𝔽)
    (hψ : ∀ x, ψ.val x = φ.val (g⁻¹ * x)) :
    kerExists(ha, hs, P, ψ) ↔ kerExists(ha, hs, P, φ) := by
  have h (g : C𝔽) (f k : BruhatCompactSupport C𝔽) (hk : ∀ x, k.val x = f.val (g⁻¹ * x))
      (hK : kerExists(ha, hs, P, f)) : kerExists(ha, hs, P, k) := by
    apply (kernelLocalization_nuclear_iff ha hs _).mpr
    rw [stripTestAction_translate ha hs g f k hk]
    exact mul_mem_nuclearEndomorphisms_left _ ⟨_, (kernelLocalization_nuclear_iff ha hs _).mp hK⟩
  exact ⟨h g⁻¹ ψ φ (fun x ↦ by simp only [inv_inv, hψ, inv_mul_cancel_left]), h g φ ψ hψ⟩

/-- For a translated test the trace norm on the strip is bounded by the endpoint
exponential times the Sobolev polynomial. This applies to any fixed input operator. -/
theorem stripTestAction_translate_traceNorm_le {α s : ℝ} (ha : 0 ≤ α) (hs : 0 ≤ s)
    (P : W(α, s) →L[ℂ] W(α, s)) (g : C𝔽) (φ ψ : BruhatCompactSupport C𝔽)
    (hψ : ∀ x, ψ.val x = φ.val (g⁻¹ * x)) (N : nuclearEndomorphisms (W(α, s)))
    (hN : N.val = (A(ha, hs, φ)).comp P) :
    ∃ M : nuclearEndomorphisms (W(α, s)), M.val = (A(ha, hs, ψ)).comp P ∧
      traceNorm M ≤ Real.exp (α * |ℓ g|) * (1 + |ℓ g|) ^ (s / 2) * traceNorm N := by
  let T := T(ha, hs, g)
  refine ⟨⟨T * N.val, mul_mem_nuclearEndomorphisms_left T N⟩, ?_, ?_⟩
  · change T * N.val = _
    rw [hN, stripTestAction_translate ha hs g φ ψ hψ]
    rfl
  · have hn : 0 ≤ traceNorm N := by
      let : Norm (nuclearEndomorphisms (W(α, s))) := ⟨traceNorm⟩
      exact (traceNorm_normedSpaceCore (H := W(α, s))).norm_nonneg N
    refine (traceNorm_mul_left_le T N).trans (mul_le_mul_of_nonneg_right ?_ hn)
    apply (norm_hardySobolevTranslation_le μ𝔽 m𝔽 (-α) α s _ hs g).trans
    apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (by positivity) _)
    apply max_le <;> apply Real.exp_le_exp.mpr
    · calc -α * ℓ g = α * (-ℓ g) := by ring
           _ ≤ α * |ℓ g| := mul_le_mul_of_nonneg_left (neg_le_abs _) ha
    · exact mul_le_mul_of_nonneg_left (le_abs_self _) ha

private theorem kernelLocalization_continuous_log : Continuous (ℓ : C𝔽 → ℝ) :=
  (NNReal.continuous_coe.comp (Units.continuous_val.comp (m𝔽).continuous)).log
    fun g ↦ NNReal.coe_ne_zero.mpr (m𝔽 g).ne_zero

private theorem kernelLocalization_log_mul (g x : C𝔽) : ℓ (g * x) = ℓ g + ℓ x := by
  change Real.log ((ideleClassNorm F (g * x)).val : ℝ) = _
  rw [map_mul, Units.val_mul, NNReal.coe_mul, Real.log_mul
    (NNReal.coe_ne_zero.mpr (ideleClassNorm F g).ne_zero)
    (NNReal.coe_ne_zero.mpr (ideleClassNorm F x).ne_zero)]

private theorem kernelLocalization_log_surjective : Function.Surjective (ℓ : C𝔽 → ℝ) := by
  intro t
  let e : ℝ ≃ₜ ℝ≥0ˣ := Real.expOrderIso.toHomeomorph.trans (Nonneg.unitsHomeomorphPos ℝ).symm
  let g : C𝔽 := QuotientGroup.mk (canonicalIdeleNormSection F (e t))
  refine ⟨g, ?_⟩
  change Real.log ((ideleClassNorm F g).val : ℝ) = _
  rw [show ideleClassNorm F g = e t from canonicalIdeleNormSection_rightInverse F (e t)]
  exact Real.log_exp _


open scoped Manifold in
private theorem kernelLocalization_real_partition {K U : Set ℝ} (hc : IsCompact K)
    (ho : IsOpen U) {u : ℝ} (hu : u ∈ U) :
    ∃ (S : Finset ℝ) (ρ : S → ℝ → ℝ), (∀ i, ContDiff ℝ ∞ (ρ i)) ∧
      (∀ i t, t ∈ tsupport (ρ i) → (u - i.val) + t ∈ U) ∧
      ∀ t ∈ K, ∑ i, ρ i t = 1 := by
  classical
  let V (t : ℝ) := (fun x : ℝ ↦ (u - t) + x) ⁻¹' U
  have hV (t : ℝ) : IsOpen (V t) := ho.preimage (continuous_const.add continuous_id)
  obtain ⟨S, hS⟩ := hc.elim_finite_subcover V hV fun t _ ↦
    mem_iUnion.mpr ⟨t, by simpa only [V, mem_preimage, sub_add_cancel] using hu⟩
  obtain ⟨ρ, hρ⟩ := SmoothPartitionOfUnity.exists_isSubordinate 𝓘(ℝ, ℝ) hc.isClosed
    (fun i : S ↦ V i.val) (fun i ↦ hV i.val) (by simpa only [iUnion_subtype] using hS)
  refine ⟨S, fun i t ↦ ρ i t, fun i ↦ contMDiff_iff_contDiff.mp (ρ i).contMDiff,
    fun i _ ht ↦ hρ i ht, fun t ht ↦ ?_⟩
  rw [← finsum_eq_sum_of_fintype]
  exact ρ.sum_eq_one ht

private def kernelLocalization_profile (φ : BruhatCompactSupport C𝔽) (r : ℝ → ℝ)
    (hr : ContDiff ℝ ∞ r) : BruhatCompactSupport C𝔽 :=
  ⟨fun x ↦ (r (ℓ x) : ℂ) * φ.val x, (mem_bruhatSmoothSubmodule_iff _).mpr fun p ↦
    isBruhatContDiff_mul (isBruhatSmooth_logProfile m𝔽 (Complex.ofRealCLM.contDiff.comp hr) p)
      ((mem_bruhatSmoothSubmodule_iff _).mp φ.property.1 p),
    (show HasCompactSupport φ.val from φ.property.2).mul_left⟩

private theorem kernelLocalization_profile_support (φ : BruhatCompactSupport C𝔽)
    (r : ℝ → ℝ) (hr : ContDiff ℝ ∞ r) :
    tsupport (kernelLocalization_profile φ r hr).val ⊆ ℓ ⁻¹' tsupport r :=
  tsupport_mul_subset_left.trans ((tsupport_comp_subset_preimage
    (fun t : ℝ ↦ (r t : ℂ)) kernelLocalization_continuous_log).trans
    (preimage_mono (tsupport_comp_subset Complex.ofReal_zero r)))

private theorem kernelLocalization_profile_sum {ι : Type*} [Fintype ι] (φ : BruhatCompactSupport C𝔽)
    (r : ι → ℝ → ℝ) (hr : ∀ i, ContDiff ℝ ∞ (r i))
    (h1 : ∀ t ∈ ℓ '' tsupport φ.val, ∑ i, r i t = 1) :
    φ = ∑ i, kernelLocalization_profile φ (r i) (hr i) := by
  classical
  apply Subtype.ext
  funext x
  let ev : BruhatCompactSupport C𝔽 →+ ℂ :=
    { toFun k := k.val x, map_zero' := rfl, map_add' := fun _ _ ↦ rfl }
  change φ.val x = ev (∑ i, kernelLocalization_profile φ (r i) (hr i))
  rw [map_sum]
  change φ.val x = ∑ i, (r i (ℓ x) : ℂ) * φ.val x
  rw [← Finset.sum_mul, ← Complex.ofReal_sum]
  by_cases hx : x ∈ tsupport φ.val
  · rw [h1 _ (mem_image_of_mem ℓ hx), Complex.ofReal_one, one_mul]
  · rw [image_eq_zero_of_notMem_tsupport hx, mul_zero]

private theorem kernelLocalization_shift_support {U : Set ℝ} (d : ℝ) (f : BruhatCompactSupport C𝔽)
    (hf : ∀ x ∈ tsupport f.val, d + ℓ x ∈ U) :
    ∃ (g : C𝔽) (ψ : BruhatCompactSupport C𝔽), tsupport ψ.val ⊆ ℓ ⁻¹' U ∧
      ∀ x, f.val x = ψ.val (g⁻¹ * x) := by
  obtain ⟨g, hg⟩ := kernelLocalization_log_surjective (F := F) d
  obtain ⟨ψ, hψ⟩ := kernelLocalization_exists_translate g f
  refine ⟨g⁻¹, ψ, ?_, fun x ↦ by simp only [inv_inv, hψ, inv_mul_cancel_left]⟩
  intro x hx
  have he : ψ.val = f.val ∘ (fun y ↦ g⁻¹ * y) := funext hψ
  have hy := hf (g⁻¹ * x) (tsupport_comp_subset_preimage f.val
    (continuous_const.mul continuous_id) (he ▸ hx))
  rwa [← hg, ← kernelLocalization_log_mul, mul_inv_cancel_left] at hy

/-- A compact Bruhat test is a finite sum of translates of tests supported in any
prescribed nonempty open log-norm set. The summands and translations depend only on
the test and the set, so the same decomposition works at every strip width. -/
theorem bruhatCompactSupport_finite_sum_translates_of_logNorm {U : Set ℝ} (ho : IsOpen U)
    (hne : U.Nonempty) (φ : BruhatCompactSupport C𝔽) :
    ∃ (S : Finset ℝ) (f ψ : S → BruhatCompactSupport C𝔽) (g : S → C𝔽),
      φ = ∑ i, f i ∧ (∀ i, tsupport (ψ i).val ⊆ ℓ ⁻¹' U) ∧
      ∀ i x, (f i).val x = (ψ i).val ((g i)⁻¹ * x) := by
  classical
  obtain ⟨u, hu⟩ := hne
  have hc : IsCompact (ℓ '' tsupport φ.val) :=
    (show HasCompactSupport φ.val from φ.property.2).image kernelLocalization_continuous_log
  obtain ⟨S, ρ, hr, hsup, hsum⟩ := kernelLocalization_real_partition hc ho hu
  let f (i : S) := kernelLocalization_profile φ (ρ i) (hr i)
  have piece (i : S) := kernelLocalization_shift_support (u - i.val) (f i)
    (fun x hx ↦ hsup i (ℓ x) (kernelLocalization_profile_support φ (ρ i) (hr i) hx))
  choose g ψ hψ he using piece
  exact ⟨S, f, ψ, g, kernelLocalization_profile_sum φ ρ hr hsum, hψ, he⟩

private theorem kernelLocalization_sum {α s : ℝ} (ha : 0 ≤ α) (hs : 0 ≤ s)
    (P : W(α, s) →L[ℂ] W(α, s)) {ι : Type*} [Fintype ι] (f : ι → BruhatCompactSupport C𝔽)
    (h : ∀ i, kerExists(ha, hs, P, f i)) : kerExists(ha, hs, P, ∑ i, f i) := by
  classical
  choose kernels hk using h
  refine ⟨∑ i, kernels i, ?_⟩
  rw [map_sum, map_sum]
  change ∑ i, sobolevProjectiveKernelOperator (F := F) ha hs (kernels i) =
    (∑ i, (A(ha, hs, f i) : W(α, s) →L[ℂ] W(α, s))).comp P
  apply ContinuousLinearMap.ext
  intro v
  simp only [sum_apply, hk]
  change ∑ i, A(ha, hs, f i) (P v) =
    (∑ i, (A(ha, hs, f i) : W(α, s) →L[ℂ] W(α, s))) (P v)
  rw [sum_apply]

/-! ## Signed cancellation between Gaussian angular powers

Rudnick and Waxman, *Angles of Gaussian primes*, §4.1, p. 13, identify the Hecke functions
of the angular powers at k and -k. The two physical angular components therefore cancel at
the same raw zero. This realizes (12.5.1.3) at every width for the tests constructed below.
-/

section

open MeasureTheory Set
open scoped ContDiff Pointwise ComplexConjugate

namespace GaussianPairDetector

private abbrev mC := ContinuousLinearMap.mul ℝ ℂ

private def box (r : ℝ) : ℝ → ℂ :=
  (Icc (-r) r).indicator (fun _ ↦ ((2 : ℂ) * r)⁻¹)

private theorem tilted_box (r : ℝ) (z : ℂ) :
    (fun x : ℝ ↦ box r x * Complex.exp (z * x)) =
      (Icc (-r) r).indicator (fun x : ℝ ↦ ((2 : ℂ) * r)⁻¹ * Complex.exp (z * x)) :=
  funext fun x ↦ (Set.indicator_mul_left (i := x) (Icc (-r) r)
    (fun _ ↦ ((2 : ℂ) * r)⁻¹) (fun y : ℝ ↦ Complex.exp (z * y))).symm

private theorem tilted_box_integrable (r : ℝ) (z : ℂ) :
    Integrable (fun x : ℝ ↦ box r x * Complex.exp (z * x)) := by
  rw [tilted_box, integrable_indicator_iff measurableSet_Icc]
  exact (by fun_prop : Continuous (fun x : ℝ ↦ ((2 : ℂ) * r)⁻¹ * Complex.exp (z * x))).integrableOn_Icc

private theorem box_laplace {r : ℝ} (hr : 0 < r) (z : ℂ) :
    bilateralLaplace (box r) z = unitIntervalLaplaceFactor ((r : ℂ) * z) := by
  rw [bilateralLaplace, tilted_box, integral_indicator measurableSet_Icc, integral_const_mul,
    integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by linarith : -r ≤ r)]
  have t := intervalIntegral.smul_integral_comp_mul_left
    (a := -1) (b := 1) (fun y : ℝ ↦ Complex.exp (z * y)) r
  simp only [mul_neg, mul_one, Complex.ofReal_mul, Complex.real_smul] at t
  have a : (fun x : ℝ ↦ Complex.exp (z * ((r : ℂ) * x))) =
      (fun x : ℝ ↦ Complex.exp (((r : ℂ) * z) * x)) := by
    funext x; congr 1; ring
  rw [← t, a, unitIntervalLaplaceFactor]
  have hrC : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hr.ne'
  field_simp

private theorem tilted_smooth_integrable {f : ℝ → ℂ} (hf : Continuous f)
    (hc : HasCompactSupport f) (z : ℂ) :
    Integrable (fun x : ℝ ↦ f x * Complex.exp (z * x)) :=
  (hf.mul (by fun_prop)).integrable_of_hasCompactSupport hc.mul_right

private theorem laplace_convolution (f g : ℝ → ℂ) (z : ℂ)
    (hf : Integrable (fun x : ℝ ↦ f x * Complex.exp (z * x)))
    (hg : Integrable (fun x : ℝ ↦ g x * Complex.exp (z * x))) :
    bilateralLaplace (convolution f g mC volume) z = bilateralLaplace f z * bilateralLaplace g z := by
  let F := fun x : ℝ ↦ f x * Complex.exp (z * x)
  let G := fun x : ℝ ↦ g x * Complex.exp (z * x)
  have mul_exp (x y : ℝ) :
      Complex.exp (z * x) = Complex.exp (z * y) * Complex.exp (z * ((x - y : ℝ) : ℂ)) := by
    rw [← Complex.exp_add, Complex.ofReal_sub]
    congr 1; ring
  have pt (x : ℝ) : convolution f g mC volume x * Complex.exp (z*x) =
      convolution F G mC volume x := by
    change (∫ y : ℝ, f y * g (x-y)) * _ = ∫ y : ℝ, F y * G (x-y)
    rw [← integral_mul_const]
    congr 1
    funext y
    change (f y * g (x-y)) * _ = (f y * _) * (g (x-y) * _)
    rw [mul_exp x y]
    ring
  unfold bilateralLaplace
  simp_rw [pt]
  exact integral_convolution mC hf hg

private def boxes (r : ℝ) : ℕ → (ℝ → ℂ) → ℝ → ℂ
  | 0, f => f
  | n + 1, f => convolution (box r) (boxes r n f) mC volume

private theorem boxes_real (r : ℝ) (n : ℕ) {f : ℝ → ℂ}
    (hf : ∀ x, conj (f x) = f x) : ∀ x, conj (boxes r n f x) = boxes r n f x := by
  induction n with
  | zero => exact hf
  | succ n ih =>
    intro x
    change conj (∫ y : ℝ, (box r y) * (boxes r n f (x-y))) = _
    rw [← integral_conj]
    change (∫ y : ℝ, conj (_ * _)) = ∫ y : ℝ, box r y * boxes r n f (x-y)
    congr 1
    funext y
    rw [map_mul,ih]
    by_cases hy : y ∈ Icc (-r) r <;> simp [box,hy,map_ofNat]

private theorem boxes_props {r : ℝ} (hr : 0 < r) (n : ℕ) {f : ℝ → ℂ}
    (hf : ContDiff ℝ ∞ f) {u v : ℝ} (hs : tsupport f ⊆ Icc u v) :
    ContDiff ℝ ∞ (boxes r n f) ∧
    tsupport (boxes r n f) ⊆ Icc (u - n*r) (v + n*r) ∧
    ∀ z, bilateralLaplace (boxes r n f) z =
      unitIntervalLaplaceFactor ((r : ℂ)*z)^n * bilateralLaplace f z := by
  induction n with
  | zero => simpa [boxes] using And.intro hf hs
  | succ n ih =>
    obtain ⟨hsm, hsup, hlap⟩ := ih
    have hc : HasCompactSupport (boxes r n f) :=
      isCompact_Icc.of_isClosed_subset (isClosed_tsupport _) hsup
    have hb : Integrable (box r) := by simpa using tilted_box_integrable r 0
    refine ⟨hc.contDiff_convolution_right mC hb.locallyIntegrable hsm,
      closure_minimal ?_ isClosed_Icc, fun z ↦ ?_⟩
    · intro x hx
      obtain ⟨a, ha, b, hb', rfl⟩ := support_convolution_subset mC hx
      have ha' : a ∈ Icc (-r) r := support_indicator_subset ha
      have hb'' := hsup (subset_tsupport _ hb')
      simp only [mem_Icc] at ha' hb'' ⊢
      push_cast
      constructor <;> nlinarith [ha'.1, ha'.2, hb''.1, hb''.2]
    · rw [boxes, laplace_convolution _ _ _ (tilted_box_integrable _ _)
          (tilted_smooth_integrable hsm.continuous hc _), box_laplace hr, hlap, pow_succ]
      ring

private theorem laplace_reflect (f : ℝ → ℂ) (z : ℂ) :
    bilateralLaplace (fun x ↦ f (-x)) z = bilateralLaplace f (-z) := by
  unfold bilateralLaplace
  simpa only [Complex.ofReal_neg, neg_mul_neg] using
    (integral_neg_eq_self (fun x : ℝ ↦ f x * Complex.exp ((-z) * x)) volume)

private theorem boxFactor_even : Function.Even unitIntervalLaplaceFactor := by
  intro z
  have t := intervalIntegral.integral_comp_neg (a := (-1:ℝ)) (b := 1)
    (f := fun x : ℝ ↦ Complex.exp (z*x))
  simpa [unitIntervalLaplaceFactor, neg_mul, mul_neg, Complex.ofReal_neg] using
    congrArg (fun w : ℂ ↦ w/2) t

private theorem quadratic_even : Function.Even quadraticBoxLaplace := by
  intro z
  unfold quadraticBoxLaplace
  apply tprod_congr
  intro i
  rw [mul_neg, boxFactor_even]


/-- Radius of each of the 172 equal intervals in the fixed detector. -/
def slabRadius : ℝ := 3 / (2 * 172)

/-- The unnormalized Laplace multiplier after the 172 additional uniform intervals. -/
def slabMultiplier (z : ℂ) : ℂ :=
  unitIntervalLaplaceFactor ((slabRadius : ℂ) * z)^172 *
    translatedIntervalMultiplier quadraticBoxLaplace z

private theorem slabMultiplier_ne_zero {z : ℂ} (hz : 0 < |z.re|) (hb : |z.re| < 1/2) :
    slabMultiplier z ≠ 0 := by
  have hRe : z.re ≠ 0 := abs_pos.mp hz
  have ha : (((slabRadius : ℂ) * z)).re ≠ 0 := by
    rw [Complex.re_ofReal_mul]
    exact mul_ne_zero (by norm_num [slabRadius]) hRe
  exact mul_ne_zero (pow_ne_zero _ (unitIntervalLaplaceFactor_ne_zero ha)) <|
    translatedIntervalMultiplier_ne_zero _ (fun _ h ↦ quadraticBoxLaplace_ne_zero h) z hz hb

private theorem slabMultiplier_polar :
    slabMultiplier (-(1/2)) = 0 ∧ slabMultiplier 0 = 0 ∧ slabMultiplier (1/2) = 0 := by
  obtain ⟨a,b,c⟩ := translatedIntervalMultiplier_polar_central quadraticBoxLaplace
  simp only [slabMultiplier,a,b,c,mul_zero,and_self]

private theorem slabMultiplier_neg (z : ℂ) :
    slabMultiplier (-z) = -Complex.exp (-6*z) * slabMultiplier z := by
  have hexp : Complex.exp (-6*z) * Complex.exp (3*z) = Complex.exp (-(3*z)) := by
    rw [← Complex.exp_add]; congr 1; ring
  unfold slabMultiplier translatedIntervalMultiplier
  rw [mul_neg, boxFactor_even, quadratic_even, mul_neg]
  rw [show (3:ℂ) * -z = -(3*z) by ring, ← hexp]
  ring

/-- The exact Laplace numerator for the odd reflection, retaining the even analytic factor. -/
theorem slabMultiplier_sub_reflected (z : ℂ) :
    slabMultiplier z - slabMultiplier (-z) =
      -2 * Complex.cosh (3*z) * z * (z^2-1/4) * quadraticBoxLaplace z *
        unitIntervalLaplaceFactor ((3/344:ℂ)*z)^172 := by
  rw [← show (slabRadius : ℂ) = 3/344 by norm_num [slabRadius]]
  unfold slabMultiplier translatedIntervalMultiplier
  rw [mul_neg,boxFactor_even,quadratic_even,mul_neg]
  rw [show (3 : ℂ) * -z = -(3*z) by ring]
  simp only [Complex.cosh]
  ring

private theorem exp_factor_ne_zero {z : ℂ} (hr : z.re ≠ 0) :
    1 + Complex.exp (-6*z) ≠ 0 := by
  intro h
  have he : Complex.exp (-6*z) = -1 := by linear_combination h
  have hn := congrArg (fun w : ℂ ↦ ‖w‖) he
  simp only [Complex.norm_exp, norm_neg, norm_one] at hn
  rw [← Real.exp_zero, Real.exp_eq_exp] at hn
  simp [Complex.mul_re] at hn
  exact hr (by linarith)

/-- Normalizing value of the polynomial and interval product before odd reflection. -/
def normAtQuarter : ℂ := slabMultiplier (1/4)
/-- Additional normalization of the odd projection at the positive quarter. -/
def oddScale : ℂ := 1 + Real.exp (-(3/2))

private theorem normAtQuarter_ne_zero : normAtQuarter ≠ 0 :=
  slabMultiplier_ne_zero (by norm_num) (by norm_num)

private theorem oddScale_ne_zero : oddScale ≠ 0 := by
  change 1 + ((Real.exp (-(3/2)) : ℝ) : ℂ) ≠ 0
  exact_mod_cast (show (1:ℝ) + Real.exp (-(3/2)) ≠ 0 by positivity)

/-- The normalized radial transform from the pinned interval profile after odd reflection. -/
def oddRadialMultiplier (z : ℂ) : ℂ :=
  (slabMultiplier z - slabMultiplier (-z)) / normAtQuarter / oddScale

theorem oddRadialMultiplier_detects {z : ℂ} (hz : 0 < |z.re|) (hb : |z.re| < 1/2) :
    oddRadialMultiplier z ≠ 0 := by
  apply div_ne_zero _ oddScale_ne_zero
  apply div_ne_zero _ normAtQuarter_ne_zero
  rw [slabMultiplier_neg z]
  convert mul_ne_zero (exp_factor_ne_zero (abs_pos.mp hz)) (slabMultiplier_ne_zero hz hb) using 1
  ring

theorem oddRadialMultiplier_references :
    oddRadialMultiplier (1/4) = 1 ∧ oddRadialMultiplier (-(1/4)) = -1 := by
  have he : Complex.exp ((-6:ℂ)*(1/4)) = (Real.exp (-(3/2)):ℝ) := by
    rw [Complex.ofReal_exp]; congr 1; push_cast; ring
  have hp : oddRadialMultiplier (1/4) = 1 := by
    unfold oddRadialMultiplier
    rw [slabMultiplier_neg (1/4), he]
    change (normAtQuarter - -(↑(Real.exp (-(3/2))):ℂ)*normAtQuarter) / normAtQuarter / oddScale = 1
    rw [div_eq_iff oddScale_ne_zero, div_eq_iff normAtQuarter_ne_zero]
    unfold oddScale
    ring
  refine ⟨hp, ?_⟩
  calc oddRadialMultiplier (-(1/4)) = -oddRadialMultiplier (1/4) := by
         simp only [oddRadialMultiplier,neg_neg]; ring
       _ = -1 := by rw [hp]

theorem oddRadialMultiplier_polar :
    oddRadialMultiplier (-(1/2)) = 0 ∧ oddRadialMultiplier 0 = 0 ∧
    oddRadialMultiplier (1/2) = 0 := by
  obtain ⟨a,b,c⟩ := slabMultiplier_polar
  simp only [oddRadialMultiplier,neg_neg,neg_zero,a,b,c,sub_self,zero_div,and_self]

private theorem laplace_sub_reflection_scaled {f : ℝ → ℂ} (hf : Continuous f)
    (hc : HasCompactSupport f) (a b z : ℂ) :
    bilateralLaplace (fun x ↦ (f x / a - f (-x) / a) / b) z =
      (bilateralLaplace f z - bilateralLaplace f (-z)) / a / b := by
  have hR : Continuous (fun x : ℝ ↦ f (-x)) := hf.comp continuous_neg
  have hcR : HasCompactSupport (fun x : ℝ ↦ f (-x)) := hc.comp_homeomorph (Homeomorph.neg ℝ)
  rw [← laplace_reflect f z]
  unfold bilateralLaplace
  rw [← integral_sub (tilted_smooth_integrable hf hc z)
    (tilted_smooth_integrable hR hcR z), ← integral_div, ← integral_div]
  congr 1; funext x; ring

/-- The sign and all factors of the odd projection in the positive bilateral Laplace convention. -/
theorem oddRadialMultiplier_formula (z : ℂ) :
    oddRadialMultiplier z =
      (-2 * Complex.cosh (3*z) * z * (z^2-1/4) * quadraticBoxLaplace z *
        unitIntervalLaplaceFactor ((3/344:ℂ)*z)^172) /
        slabMultiplier (1/4) / (1 + (Real.exp (-(3/2)) : ℝ)) := by
  rw [oddRadialMultiplier,slabMultiplier_sub_reflected]
  rfl

/-- The literal 172-box calibration admits a compact smooth odd radial representative,
with the stated support and exactly the normalized bilateral Laplace coefficients. -/
theorem exists_oddRadialDetector :
    ∃ g : ℝ → ℂ, ContDiff ℝ ∞ g ∧ HasCompactSupport g ∧ Function.Odd g ∧
      tsupport g ⊆ Icc (-(11/2)) (-(1/2)) ∪ Icc (1/2) (11/2) ∧
      (∀ x, conj (g x) = g x) ∧ (∃ x, g x ≠ 0) ∧
      ∀ z, bilateralLaplace g z = oddRadialMultiplier z := by
  obtain ⟨H, hM, hsm, hsup, _⟩ := exists_translatedGevreyPolarProfile
  let f : ℝ → ℂ := boxes slabRadius 172 (fun x ↦ (H x : ℂ))
  have hsup' : tsupport (fun x ↦ (H x : ℂ)) ⊆ Icc 2 4 :=
    (tsupport_comp_subset (g := Complex.ofReal) rfl H).trans hsup
  obtain ⟨hs,hS,hL⟩ := boxes_props (f := fun x ↦ (H x : ℂ))
    (r := slabRadius) (by norm_num [slabRadius]) 172
    (Complex.ofRealCLM.contDiff.comp hsm) hsup'
  have hs' : ContDiff ℝ ∞ f := hs
  have hS' : tsupport f ⊆ Icc (1/2) (11/2) := by
    have h1 : (2 : ℝ) - 172 * slabRadius = 1/2 := by norm_num [slabRadius]
    have h2 : (4 : ℝ) + 172 * slabRadius = 11/2 := by norm_num [slabRadius]
    simpa only [Nat.cast_ofNat, h1, h2] using hS
  have hc : HasCompactSupport f := isCompact_Icc.of_isClosed_subset (isClosed_tsupport _) hS'
  have hL' (z : ℂ) : bilateralLaplace f z = slabMultiplier z := by
    rw [show bilateralLaplace f z = _ from hL z, hM]; rfl
  let g : ℝ → ℂ := fun x ↦ (f x / normAtQuarter - f (-x) / normAtQuarter) / oddScale
  have hgs : ContDiff ℝ ∞ g :=
    ((hs'.div_const _).sub ((hs'.comp contDiff_id.neg).div_const _)).div_const _
  have hgS : tsupport g ⊆ Icc (-(11/2)) (-(1/2)) ∪ Icc (1/2) (11/2) := by
    refine closure_minimal ?_ (isClosed_Icc.union isClosed_Icc)
    intro x hx
    by_contra hnot
    have hxf : x ∉ tsupport f := fun h ↦ hnot (Or.inr (hS' h))
    have hnf : -x ∉ tsupport f := by
      intro h
      obtain ⟨hn1,hn2⟩ := hS' h
      apply hnot
      exact Or.inl ⟨by linarith, by linarith⟩
    apply hx
    simp [g,image_eq_zero_of_notMem_tsupport hxf,image_eq_zero_of_notMem_tsupport hnf]
  have hfg (z : ℂ) : bilateralLaplace g z = oddRadialMultiplier z := by
    rw [show bilateralLaplace g z = _ from laplace_sub_reflection_scaled hs'.continuous hc _ _ z,
      hL', hL']; rfl
  have hreal (x : ℝ) : conj (f x) = f x :=
    boxes_real slabRadius 172 (f := fun y ↦ (H y : ℂ)) (by simp) x
  have hq : conj normAtQuarter = normAtQuarter := by
    change conj (slabMultiplier (1/4)) = slabMultiplier (1/4)
    rw [← hL']
    unfold bilateralLaplace
    rw [← integral_conj]
    congr 1; funext x
    simp only [map_mul, hreal, ← Complex.exp_conj, map_div₀, map_one, map_ofNat,
      Complex.conj_ofReal]
  have hD : conj oddScale = oddScale := by
    simp only [oddScale,map_add,map_one,Complex.conj_ofReal]
  refine ⟨g,hgs,(isCompact_Icc.union isCompact_Icc).of_isClosed_subset (isClosed_tsupport _) hgS,
    fun x ↦ ?_,hgS,fun x ↦ ?_,?_,hfg⟩
  · simp only [g,neg_neg]; ring
  · simp only [g,map_div₀,map_sub,hreal,hq,hD]
  · by_contra! hnone
    have h1 := (hfg (1/4)).trans oddRadialMultiplier_references.1
    simp [bilateralLaplace,hnone] at h1

end GaussianPairDetector



open MeasureTheory NumberField Function
open scoped NNReal ContDiff

namespace GaussianPairDetector

attribute [local instance] instIdeleClassMeasurableSpaceSec1 instIdeleClassBorelSpaceSec1
  instIdeleClassT2Sec1 instIdeleClassLocallyCompactSec1 instIdeleClassSecondCountableSec1
  instIdeleClassHaarMeasureSec1

variable {F : Type*} [Field F] [NumberField F]
local notation "Gψ" => IdeleClassGroup (𝓞 F) F

/-- The product of the inverse-antisymmetric angular coefficient and an odd radial
test gives an inversion-even compact Bruhat function. For normalized non-self-inverse
characters, nonvanishing of the radial test makes the genuine compact function nonzero. -/
theorem exists_inversionEven_characterPairTest
    (τ : ℝ≥0ˣ →ₜ* Gψ) (hτ : RightInverse τ (ideleClassNorm F)) (χ : PontryaginDual Gψ)
    (hχ : ∀ t, χ (τ t) = 1) (hne : χ ≠ χ⁻¹) {g : ℝ → ℂ}
    (hs : ContDiff ℝ ∞ g) (hc : HasCompactSupport g) (ho : Function.Odd g)
    (hn : ∃ t, g t ≠ 0) {V : ℂ} (hV : V ≠ 0) :
    ∃ φ : BruhatCompactSupport Gψ,
      (∀ x, φ.val x = ((χ⁻¹ x : ℂ) - (χ x : ℂ)) * g (logIdeleClassNorm F x) / V) ∧
      (∀ x, φ.val x⁻¹ = φ.val x) ∧ (∀ u : (ideleClassNorm F).ker, φ.val u.val = 0) ∧
      ∃ x, φ.val x ≠ 0 := by
  obtain ⟨p,hp⟩ := exists_characterNormTest (F := F) χ⁻¹ _ hs hc
  obtain ⟨q,hq⟩ := exists_characterNormTest (F := F) χ _ hs hc
  let φ : BruhatCompactSupport Gψ := V⁻¹ • (p - q)
  have hφ (x : Gψ) :
      φ.val x = ((χ⁻¹ x : ℂ) - (χ x : ℂ)) * g (logIdeleClassNorm F x) / V := by
    change V⁻¹ * (p.val x - q.val x) = _
    rw [hp,hq]
    change V⁻¹ * ((χ⁻¹ x : ℂ) * g (logIdeleClassNorm F x) -
      (χ x : ℂ) * g (logIdeleClassNorm F x)) = _
    ring
  have hzero : g 0 = 0 := by
    have h := ho 0
    rw [neg_zero] at h
    linear_combination h/2
  refine ⟨φ,hφ,fun x ↦ ?_,fun u ↦ ?_,?_⟩
  · have hL : logIdeleClassNorm F x⁻¹ = -(logIdeleClassNorm F x) := by
      change Real.log _ = -Real.log _
      simp [map_inv]
    rw [hφ,hφ,hL,ho]
    simp only [map_inv, show χ⁻¹ x = (χ x)⁻¹ from rfl, inv_inv]
    ring
  · rw [hφ]
    have hL : logIdeleClassNorm F u.val = 0 := by
      change Real.log ((ideleClassNorm F u.val).val : ℝ) = 0
      rw [show ideleClassNorm F u.val = 1 from u.property]
      simp
    rw [hL,hzero,mul_zero,zero_div]
  · obtain ⟨y,hy⟩ : ∃ y, χ y ≠ χ⁻¹ y :=
      not_forall.mp fun h ↦ hne (DFunLike.ext _ _ h)
    obtain ⟨t,ht⟩ := hn
    let e : ℝ ≃ₜ ℝ≥0ˣ :=
      Real.expOrderIso.toHomeomorph.trans (Nonneg.unitsHomeomorphPos ℝ).symm
    let x : Gψ := y * (τ (ideleClassNorm F y))⁻¹ * τ (e t)
    have hL : logIdeleClassNorm F x = t := by
      change Real.log ((ideleClassNorm F x).val : ℝ) = t
      rw [show ideleClassNorm F x = e t by simp [x,hτ _]]
      exact Real.log_exp t
    have hx : χ x = χ y := by simp [x,hχ]
    have hx' : χ⁻¹ x = χ⁻¹ y := congrArg Inv.inv hx
    refine ⟨x,?_⟩
    rw [hφ,hL,hx,hx']
    exact div_ne_zero (mul_ne_zero (sub_ne_zero.mpr (fun he ↦ hy (Subtype.ext he.symm))) ht) hV

end GaussianPairDetector

end

section

open Filter Function IsDedekindDomain NumberField Set
open scoped Topology NumberField.AdeleRing

section

noncomputable section

set_option quotPrecheck false

variable {F : Type*} [Field F] [NumberField F]

local notation "Gψ" => IdeleClassGroup (𝓞 F) F
local notation "U" => PontryaginDual Gψ
local notation "D(" χ ", " z ")" => MeromorphicOn.divisor (continuedCompletedHeckeL (F := F) χ) univ z
local notation "P" => HeightOneSpectrum (𝓞 F)
local notation "R" => {s : ℂ // 1 < s.re}

/-- An arbitrary relabeling of the finite Euler factors preserves the actual finite
Hecke L-function throughout the half-plane of absolute convergence. -/
theorem finiteHeckeL_eq_of_eulerPermutation (χ ψ : U) (e : Equiv.Perm P)
    (he : ∀ (v : P) (s : R), finiteHeckeEulerFactor χ v s = finiteHeckeEulerFactor ψ (e v) s)
    (s : R) : finiteHeckeL χ s = finiteHeckeL ψ s := by
  have hi := (e.hasProd_iff (f := fun v ↦ finiteHeckeEulerFactor ψ v s)).2 (finiteHeckeL_hasProd ψ s)
  exact (finiteHeckeL_hasProd χ s).unique (hi.congr_fun fun v ↦ he v s)

/-- Equality of the finite Euler L-functions and the archimedean factors on the
half-plane of absolute convergence identifies the native meromorphic completions
at every point, in the project's chosen normal form even at poles. -/
theorem continuedCompletedHeckeL_eq_of_gamma_and_finite (χ ψ : U)
    (hΓ : ∀ s : R, heckeGammaFactor χ s = heckeGammaFactor ψ s)
    (hfinite : ∀ s : R, finiteHeckeL χ s = finiteHeckeL ψ s) :
    continuedCompletedHeckeL χ = continuedCompletedHeckeL ψ := by
  obtain ⟨mχ, hχ⟩ := continuedCompletedHeckeL_spec χ
  obtain ⟨mψ, hψ⟩ := continuedCompletedHeckeL_spec ψ
  have hzero : meromorphicOrderAt (continuedCompletedHeckeL χ - continuedCompletedHeckeL ψ) (2 : ℂ) = ⊤ := by
    apply meromorphicOrderAt_eq_top_iff.mpr
    have hh : ∀ᶠ s : ℂ in 𝓝 (2 : ℂ), 1 < s.re :=
      (isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by norm_num)
    filter_upwards [hh.filter_mono nhdsWithin_le_nhds] with z hz
    apply sub_eq_zero.mpr
    let s : R := ⟨z, hz⟩
    exact (hχ s).trans ((congrArg₂ (· * ·) (hΓ s) (hfinite s)).trans (hψ s).symm)
  funext z
  have ho := (mχ.meromorphicOn.sub mψ.meromorphicOn).meromorphicOrderAt_eq_top_of_isPreconnected
    isPreconnected_univ (mem_univ (2 : ℂ)) (mem_univ z) hzero
  have he := (meromorphicOrderAt_eq_top_iff.mp ho).mono fun x hx ↦ sub_eq_zero.mp hx
  exact (((mχ (mem_univ z)).eventuallyEq_nhdsNE_iff_eventuallyEq_nhds (mψ (mem_univ z))).mp he).eq_of_nhds


end
end

end

section

open Set Function IsDedekindDomain NumberField NumberField.Gaussian
open scoped WithZero ComplexConjugate IsDedekindDomain.FiniteAdeleRing RestrictedProduct NNReal
namespace AngularPair.Gaussian

set_option quotPrecheck false

local notation "K" => CyclotomicField 4 ℚ
local notation "V" => HeightOneSpectrum (𝓞 K)
local notation "S₀" => (∅ : Finset V)
local notation "E" => InfinitePlace.Completion.extensionEmbedding place
local notation "C" => IdeleClassGroup (𝓞 K) K
local notation "ιᶜ" => (⟨Circle.coeHom, continuous_subtype_val⟩ : Circle →ₜ* ℂ)
local notation "Sep" => ContinuousMulEquiv.prodUnits (InfiniteAdeleRing K) ((v : S₀) → v.val.adicCompletion K)
local notation "Arch" => ContinuousMulEquiv.piUnits (M := fun w : InfinitePlace K ↦ w.Completion)
local notation "quot" => (QuotientGroup.mk' (IdeleGroup.principalSubgroup (𝓞 K) K))

/-- The phase of a nonzero complex number to fourth power. -/
private def phase (z : ℂ) : ℂ := (z / (‖z‖ : ℂ)) ^ 4

private theorem stage_phase :
    ∃ η : PontryaginDual (SIdeleQuotient K S₀), ∀ g : (SAdeleRing K S₀)ˣ,
      (η (QuotientGroup.mk g) : ℂ) = phase (E (g.val.1 place)) := by
  classical
  have h4 (u : (𝓞 K)ˣ) : u^4 = 1 := by
    let e := Units.mapEquiv integersEquiv.toMulEquiv
    obtain ⟨v,rfl⟩ := e.surjective u
    rw [← map_pow, GaussianInt.unit_pow_four, map_one]
  let gen₀ (v : S₀) : 𝓞 K := False.elim (Finset.notMem_empty _ v.property)
  obtain ⟨η, hη, _⟩ := exists_sLocal_fourthAngularCharacter place gen₀
    (fun v ↦ False.elim (Finset.notMem_empty _ v.property)) h4
  refine ⟨η, fun g ↦ ?_⟩
  let z := Arch (Sep g).1 place
  let ins := (Sep).symm ((Arch).symm (@Pi.mulSingle _ _ _ (Classical.decEq _) place z), 1)
  have hi : ins = g := by
    apply (Sep).injective
    rw [ContinuousMulEquiv.apply_symm_apply]
    apply Prod.ext
    · apply (Arch).injective
      rw [ContinuousMulEquiv.apply_symm_apply]
      ext v
      obtain rfl := eq_place v
      simp [z]
    · exact Subsingleton.elim _ _
  have hh := hη z
  change ((η (QuotientGroup.mk ins) : Circle) : ℂ) * _ ^ (0 : ℂ) = _ at hh
  rw [Complex.cpow_zero, mul_one, hi] at hh
  exact hh

/-- A genuinely unramified global Gaussian character with its value on all ideles
whose finite coordinates are units. -/
private theorem exists_unramified_angular :
    ∃ ψ : PontryaginDual C, ιᶜ.comp ψ ∈ unramifiedOutside K S₀ ∧
      ∀ u : (integralAdelesOutside K S₀)ˣ, (ψ (quot (integralIdeleInsertion K S₀ u)) : ℂ) =
        phase (E (u.val.val.1 place)) := by
  obtain ⟨η, hη⟩ := stage_phase
  obtain ⟨ψ, hψ, hres⟩ := exists_unitary_unramifiedOutside_extension η
  refine ⟨ψ, hψ, fun u ↦ ?_⟩
  let c : unramifiedOutside K S₀ := ⟨ιᶜ.comp ψ,hψ⟩
  let g := Units.map (adeleProjection K S₀).toMonoidHom (integralIdeleInsertion K S₀ u)
  have h := normOneCharacterUnramifiedOutside_iff_reinsert c u
  rw [← sIdeleRestriction_mk, show sIdeleRestriction K S₀ c = ιᶜ.comp η from hres] at h
  exact h.trans (hη g)

private theorem finite_unit_representative (a : IdeleGroup (𝓞 K) K) (z : Kˣ)
    (hz : ∀ v : V, Valued.v (a.val.2 v) = v.valuation K z.val) :
    ∃ u : (integralAdelesOutside K S₀)ˣ, quot (integralIdeleInsertion K S₀ u) = quot a ∧
      u.val.val.1 place = a.val.1 place / algebraMap K place.Completion z.val := by
  let p := IdeleGroup.unitEmbedding (𝓞 K) K z
  let b := a / p
  have hp : quot p = 1 := (QuotientGroup.eq_one_iff p).2 ⟨z,rfl⟩
  have hb : b ∈ Set.range (integralIdeleInsertion K S₀) := by
    apply (mem_range_integralIdeleInsertion K S₀ b).mpr
    intro v _
    let V₀ := v.adicCompletion K
    let r : NumberField.AdeleRing (𝓞 K) K →+* V₀ :=
      (RestrictedProduct.evalRingHom _ v).comp (RingHom.snd _ _)
    let R := Units.map r.toMonoidHom
    have hRz : ((R p : V₀ˣ) : V₀) = ((z : K) : v.adicCompletion K) :=
      AdeleRing.algebraMap_snd_apply (𝓞 K) K (z : K) v
    have hRV : Valued.v ((R b : V₀ˣ) : V₀) = 1 := by
      change Valued.v (((R (a / p) : V₀ˣ) : V₀)) = 1
      rw [map_div, Units.val_div_eq_div_val, Valuation.map_div, hRz,
        HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
      change Valued.v (a.val.2 v) / v.valuation K (z : K) = 1
      rw [hz, div_self ((Valuation.ne_zero_iff _).mpr z.ne_zero)]
    have h₁ : Valued.v (b.val.2 v) = 1 := hRV
    have h₂ : Valued.v (b.inv.2 v) = 1 := by
      change Valued.v ((R b)⁻¹ : V₀ˣ).val = 1
      rw [Units.val_inv_eq_inv_val, map_inv₀, hRV, inv_one]
    exact ⟨h₁.le, h₂.le⟩
  obtain ⟨u,hu⟩ := hb
  refine ⟨u, by rw [hu]; change quot (a / p) = _; rw [map_div, hp, div_one], ?_⟩
  calc
    _ = b.val.1 place := congrArg (fun g : IdeleGroup (𝓞 K) K ↦ g.val.1 place) hu
    _ = _ := by
      let r : AdeleRing (𝓞 K) K →+* place.Completion :=
        (Pi.evalRingHom (fun v : InfinitePlace K ↦ v.Completion) place).comp (RingHom.fst _ _)
      let R := Units.map r.toMonoidHom
      change (R (a / p)).val = _
      rw [map_div, Units.val_div_eq_div_val, AbsoluteValue.Completion.algebraMap_def]
      exact congrArg (fun y : place.Completion ↦ a.val.1 place / y)
        (AdeleRing.algebraMap_fst_apply (𝓞 K) K (z : K) place)

private theorem unit_formula (ψ : PontryaginDual C)
    (hψ : ∀ u : (integralAdelesOutside K S₀)ˣ,
      (ψ (quot (integralIdeleInsertion K S₀ u)) : ℂ) = phase (E (u.val.val.1 place)))
    (v : V) (g : 𝓞 K) (hg : v.asIdeal = Ideal.span {g}) :
    let t : Kˣ := Units.mk0 (g : K) ((map_ne_zero_iff _ (IsFractionRing.injective (𝓞 K) K)).2
      (primeGenerator_ne_zero v g hg))
    let π := Units.map (algebraMap K (v.adicCompletion K)).toMonoidHom t
    (ψ (IdeleClassGroup.ofAdicCompletion (𝓞 K) K v π) : ℂ) = (phase (place.embedding (g : K)))⁻¹ := by
  classical
  intro t π
  let a := IdeleGroup.ofAdicCompletion (𝓞 K) K v π
  have hv (w : V) : Valued.v (a.val.2 w) = w.valuation K t.val := by
    change Valued.v (RestrictedProduct.mulSingle (fun u : V ↦ u.adicCompletionIntegers K) v π.val w) =
      w.valuation K (algebraMap (𝓞 K) K g)
    rw [valuation_primeGenerator K w v g hg]
    rcases eq_or_ne w v with rfl | h
    · rw [RestrictedProduct.mulSingle_eq_same, ite_eq_left rfl]
      change Valued.v ((g : K) : w.adicCompletion K) = _
      rw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
      exact (valuation_primeGenerator K w w g hg).trans (ite_eq_left rfl)
    · rw [RestrictedProduct.mulSingle_eq_of_ne _ _ h, ite_eq_right h, map_one]
  obtain ⟨u, hu, hcoord⟩ := finite_unit_representative a t hv
  have h := hψ u
  change (ψ (quot a) : ℂ) = _
  rw [hu, hcoord] at h
  refine h.trans ?_
  change phase (E (1 / algebraMap K place.Completion t.val)) = _
  rw [map_div₀, map_one, one_div, AbsoluteValue.Completion.algebraMap_def,
    InfinitePlace.Completion.extensionEmbedding_coe]
  change phase (place.embedding (g : K))⁻¹ = _
  simp only [phase, norm_inv, Complex.ofReal_inv, inv_div_inv, ← inv_pow, inv_div]

private theorem section_formula (ψ : PontryaginDual C)
    (hψ : ∀ u : (integralAdelesOutside K S₀)ˣ,
      (ψ (quot (integralIdeleInsertion K S₀ u)) : ℂ) = phase (E (u.val.val.1 place)))
    (t : ℝ≥0ˣ) : ψ (quot (canonicalIdeleNormSection K t)) = 1 := by
  let a := canonicalIdeleNormSection K t
  have hz (v : V) : Valued.v (a.val.2 v) = v.valuation K (1 : Kˣ).val := by
    change Valued.v ((canonicalIdeleNormSection K t).val.2 v) = v.valuation K 1
    rw [canonicalIdeleNormSection_finite, map_one]
    exact map_one _
  obtain ⟨u,hu,hcoord⟩ := finite_unit_representative a 1 hz
  apply Circle.ext
  have hp := hψ u
  rw [hu, hcoord] at hp
  refine hp.trans ?_
  change phase (E ((canonicalIdeleNormSection K t).val.1 place / algebraMap K place.Completion 1)) = 1
  rw [map_one, div_one, canonicalIdeleNormSection_infinite]
  have hr : 0 < (t.val : ℝ) ^ (Module.finrank ℚ K : ℝ)⁻¹ :=
    Real.rpow_pos_of_pos (NNReal.coe_pos.mpr t.ne_zero.bot_lt) _
  simp [phase, Complex.norm_real, Real.norm_of_nonneg hr.le, hr.ne']

private def conjugateIntegers : (𝓞 K) ≃+* (𝓞 K) :=
  integersEquiv.symm.trans ((starRingAut : GaussianInt ≃+* GaussianInt).trans integersEquiv)

/-- The permutation of Gaussian finite primes induced by ordinary complex conjugation. -/
@[no_expose] def conjugatePrime : Equiv.Perm V := HeightOneSpectrum.equivOfRingEquiv conjugateIntegers

private theorem conjugatePrime_generator (v : V) (g : 𝓞 K) (hg : v.asIdeal = Ideal.span {g}) :
    (conjugatePrime v).asIdeal = Ideal.span {conjugateIntegers g} := by
  change (v.asIdeal.comap conjugateIntegers.symm) = _
  rw [Ideal.comap_symm, hg, Ideal.map_span, Set.image_singleton]

private theorem conjugatePrime_norm (v : V) :
    (conjugatePrime v).asIdeal.absNorm = v.asIdeal.absNorm := by
  change (v.asIdeal.comap conjugateIntegers.symm).absNorm = _
  rw [Ideal.comap_symm]
  exact Ideal.absNorm_map_ringEquiv conjugateIntegers _

private theorem embedding_conjugateIntegers (g : 𝓞 K) :
    place.embedding (conjugateIntegers g : K) = conj (place.embedding (g : K)) := by
  obtain ⟨a,rfl⟩ := integersEquiv.surjective g
  change place.embedding (integersEquiv (star (integersEquiv.symm (integersEquiv a))) : K) = _
  simp only [RingEquiv.symm_apply_apply, embedding_integersEquiv]
  exact GaussianInt.toComplex_star a

private theorem phase_conj {z : ℂ} (hz : z ≠ 0) : phase (conj z) = (phase z)⁻¹ := by
  have hn : (‖z‖ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hz)
  have hprod : z * conj z = (‖z‖ : ℂ)^2 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, Complex.ofReal_pow]
  have hdiv : conj z / (‖z‖ : ℂ) = (z / (‖z‖ : ℂ))⁻¹ := by
    rw [inv_div]
    field_simp [hn,hz]
    linear_combination hprod
  simp only [phase, Complex.norm_conj, hdiv, inv_pow]

private theorem eval_power (ψ : PontryaginDual C) (k : ℤ) (x : C) : (ψ^k) x = (ψ x)^k := by
  let ev : PontryaginDual C →* Circle := ⟨⟨fun χ ↦ χ x, rfl⟩, fun _ _ ↦ rfl⟩
  exact ev.map_zpow ψ k

private theorem powers_unramified (ψ : PontryaginDual C) (hu : ιᶜ.comp ψ ∈ unramifiedOutside K S₀)
    (k : ℤ) (v : V) : (ideleClassNormTwist (ψ ^ k) 0).IsUnramifiedAt v := by
  have hp : ideleClassNormTwist (ψ ^ k) 0 ∈ unramifiedOutside K S₀ := by
    apply (mem_unramifiedOutside_iff K S₀ _).mpr
    intro w hw u
    let x := IdeleClassGroup.ofAdicCompletion (𝓞 K) K w
      (Units.map (w.adicCompletionIntegers K).subtype.toMonoidHom u)
    have hval : (ψ x : ℂ) = 1 := (mem_unramifiedOutside_iff K S₀ _).mp hu w hw u
    change ((ψ^k) x : ℂ) * _ ^ (0 : ℂ) = 1
    rw [eval_power, Circle.coe_zpow, hval, one_zpow, Complex.cpow_zero, mul_one]
  exact hp v (Finset.notMem_empty _)

private theorem powers_localValue (ψ : PontryaginDual C) (hu : ιᶜ.comp ψ ∈ unramifiedOutside K S₀)
    (hψ : ∀ u : (integralAdelesOutside K S₀)ˣ,
      (ψ (quot (integralIdeleInsertion K S₀ u)) : ℂ) = phase (E (u.val.val.1 place)))
    (k : ℤ) (v : V) (g : 𝓞 K) (hg : v.asIdeal = Ideal.span {g}) :
    (ideleClassNormTwist (ψ^k) 0).localValue v = ((phase (place.embedding (g : K)))⁻¹)^k := by
  let t := Units.mk0 (g : K) ((map_ne_zero_iff _ (IsFractionRing.injective (𝓞 K) K)).2
    (primeGenerator_ne_zero v g hg))
  let π := Units.map (algebraMap K (v.adicCompletion K)).toMonoidHom t
  have hπ : Valued.v.IsUniformizer π.val := by
    have h : Valued.v π.val = WithZero.exp (-1 : ℤ) := by
      change Valued.v ((g : K) : v.adicCompletion K) = _
      rw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
      exact (valuation_primeGenerator K v v g hg).trans (ite_eq_left rfl)
    exact h.trans (congrArg Units.val (Valuation.IsRankOneDiscrete.generator_eq_exp_neg_one_of_surjective
      (v.valuedAdicCompletion_surjective K))).symm
  rw [(powers_unramified ψ hu k v).localValue_eq _ hπ, HeckeCharacter.restrict, MulChar.ofUnitHom_coe]
  change ((ψ^k) (IdeleClassGroup.ofAdicCompletion (𝓞 K) K v π) : ℂ) * _ ^ (0 : ℂ) = _
  rw [Complex.cpow_zero, mul_one, eval_power, Circle.coe_zpow, unit_formula ψ hψ v g hg]

private theorem has_generator (v : V) : ∃ g : 𝓞 K, v.asIdeal = Ideal.span {g} := by
  let : IsPrincipalIdealRing (𝓞 K) := IsPrincipalIdealRing.of_surjective integersEquiv.toRingHom integersEquiv.surjective
  exact ⟨(Submodule.IsPrincipal.generator v.asIdeal), (Ideal.span_singleton_generator _).symm⟩

private theorem angular_parameters (ψ : PontryaginDual C)
    (hψ : ∀ u : (integralAdelesOutside K S₀)ˣ,
      (ψ (quot (integralIdeleInsertion K S₀ u)) : ℂ) = phase (E (u.val.val.1 place)))
    (k : ℤ) : (complexHeckeCharacter_parameters (ψ^k) place isComplex_place).exists.choose = (0,4*k) := by
  classical
  apply (complexHeckeCharacter_parameters (ψ^k) place isComplex_place).unique
    (complexHeckeCharacter_parameters (ψ^k) place isComplex_place).exists.choose_spec
  refine ⟨rfl,fun x ↦ ?_⟩
  let e := InfinitePlace.Completion.ringEquivComplexOfIsComplex isComplex_place
  let z := Units.map e.symm.toMonoidHom x
  let a := IdeleGroup.ofCompletion (𝓞 K) K place z
  have hv (v : V) : Valued.v (a.val.2 v) = v.valuation K (1 : Kˣ).val := by
    change Valued.v (1 : v.adicCompletion K) = v.valuation K 1
    rw [map_one, map_one]
  obtain ⟨u, hu, hcoord⟩ := finite_unit_representative a 1 hv
  have hz : a.val.1 place = z.val := by
    change Pi.mulSingle place z.val place = _
    exact Pi.mulSingle_eq_same _ _
  have he : E z.val = (x : ℂ) := e.apply_symm_apply x.val
  have h := hψ u
  rw [hu, hcoord, hz] at h
  change (ψ (quot a) : ℂ) = phase (E (z.val / algebraMap K place.Completion 1)) at h
  rw [map_one, div_one, he] at h
  change ((ψ^k) (quot a) : ℂ) * _ ^ (0:ℂ) = _ ^ (0:ℂ) * _ ^ (4*k : ℤ)
  rw [eval_power, Circle.coe_zpow, h, Complex.cpow_zero, Complex.cpow_zero, mul_one, one_mul, zpow_mul]
  rfl

/-- A global Gaussian idèle-class character with fourth angular weight at infinity.
Every local unit at a finite place lies in its kernel. -/
@[no_expose] def globalAngularCharacter : PontryaginDual C := exists_unramified_angular.choose

private theorem globalAngularCharacter_spec :
    ιᶜ.comp globalAngularCharacter ∈ unramifiedOutside K S₀ ∧
      ∀ u : (integralAdelesOutside K S₀)ˣ,
        (globalAngularCharacter (quot (integralIdeleInsertion K S₀ u)) : ℂ) =
          phase (E (u.val.val.1 place)) :=
  exists_unramified_angular.choose_spec

/-- The canonical positive real norm section has trivial angular value. -/
theorem globalAngularCharacter_normSection (t : ℝ≥0ˣ) :
    globalAngularCharacter (quot (canonicalIdeleNormSection K t)) = 1 :=
  section_formula _ globalAngularCharacter_spec.2 t

/-- The radial exponent is zero and the oriented complex angular degree of the
`k`-th power is exactly `4k`. -/
theorem globalAngularCharacter_power_parameters (k : ℤ) :
    (complexHeckeCharacter_parameters (globalAngularCharacter ^ k) place isComplex_place).exists.choose =
      (0, 4 * k) :=
  angular_parameters _ globalAngularCharacter_spec.2 k

/-- All the integer powers are distinct as characters of the full Gaussian idèle class group. -/
theorem globalAngularCharacter_power_injective :
    Function.Injective (fun k : ℤ ↦ globalAngularCharacter ^ k) := by
  intro k l hkl
  have e := congrArg (fun η : PontryaginDual C ↦
    (complexHeckeCharacter_parameters η place isComplex_place).exists.choose.2) hkl
  change (complexHeckeCharacter_parameters (globalAngularCharacter^k) place isComplex_place).exists.choose.2 =
    (complexHeckeCharacter_parameters (globalAngularCharacter^l) place isComplex_place).exists.choose.2 at e
  rw [globalAngularCharacter_power_parameters, globalAngularCharacter_power_parameters] at e
  omega

/-- Every integer power is unramified at every finite prime, including the prime over two. -/
theorem globalAngularCharacter_power_unramified (k : ℤ) (v : V) :
    (ideleClassNormTwist (globalAngularCharacter ^ k) 0).IsUnramifiedAt v :=
  powers_unramified _ globalAngularCharacter_spec.1 k v

/-- If a Gaussian prime has generator `g`, the local uniformizer value of the `k`-th
power is the inverse `k`-th power of the fourth archimedean phase of `g`. Thus its ideal
character is `Ξ₋ₖ` in Rudnick and Waxman, §4.1. -/
theorem globalAngularCharacter_power_localValue (k : ℤ) (v : V) (g : 𝓞 K)
    (hg : v.asIdeal = Ideal.span {g}) :
    (ideleClassNormTwist (globalAngularCharacter ^ k) 0).localValue v =
      (((place.embedding (g : K) / (‖place.embedding (g : K)‖ : ℂ)) ^ (4 : ℕ))⁻¹) ^ k :=
  powers_localValue _ globalAngularCharacter_spec.1 globalAngularCharacter_spec.2 k v g hg

/-- The completed factor at the unique complex place retains its exact project
normalization, which is invariant under exchange of the two angular signs. -/
theorem globalAngularCharacter_power_gammaFactor (k : ℤ) (s : ℂ) :
    heckeGammaFactor (globalAngularCharacter ^ k) s =
      Complex.Gammaℂ (s + ((4*k).natAbs : ℂ) / 2) / 2 := by
  let : Subsingleton (InfinitePlace K) := ⟨fun x y ↦ (eq_place x).trans (eq_place y).symm⟩
  rw [heckeGammaFactor, Fintype.prod_subsingleton _ place,
    dite_eq_right (InfinitePlace.not_isReal_iff_isComplex.mpr isComplex_place),
    globalAngularCharacter_power_parameters]
  simp only [add_zero]

/-- Gaussian conjugation sends each local Euler factor to the factor of the inverse
character at the conjugate prime, for every complex argument. -/
theorem globalAngularCharacter_power_eulerFactor (k : ℤ) (v : V) (s : ℂ) :
    finiteHeckeEulerFactor (globalAngularCharacter^k) v s =
      finiteHeckeEulerFactor (globalAngularCharacter^k)⁻¹ (conjugatePrime v) s := by
  obtain ⟨g, hg⟩ := has_generator v
  have hg₀ := (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 K) K)).mpr (primeGenerator_ne_zero v g hg)
  rw [← zpow_neg, finiteHeckeEulerFactor, finiteHeckeEulerFactor,
    ite_eq_left (globalAngularCharacter_power_unramified k v),
    ite_eq_left (globalAngularCharacter_power_unramified (-k) (conjugatePrime v)),
    powers_localValue _ globalAngularCharacter_spec.1 globalAngularCharacter_spec.2 k v g hg,
    powers_localValue _ globalAngularCharacter_spec.1 globalAngularCharacter_spec.2 (-k)
      (conjugatePrime v) (conjugateIntegers g) (conjugatePrime_generator v g hg),
    conjugatePrime_norm, embedding_conjugateIntegers, phase_conj ((map_ne_zero _).mpr hg₀),
    inv_inv, zpow_neg, inv_zpow]

/-- The archimedean factor agrees at the same argument for both members of each pair. -/
theorem globalAngularCharacter_power_gammaFactor_inv (k : ℤ) (s : ℂ) :
    heckeGammaFactor (globalAngularCharacter^k) s = heckeGammaFactor (globalAngularCharacter^k)⁻¹ s := by
  rw [← zpow_neg, globalAngularCharacter_power_gammaFactor, globalAngularCharacter_power_gammaFactor,
    mul_neg, Int.natAbs_neg]

end AngularPair.Gaussian

end

section

open IsDedekindDomain NumberField NumberField.Gaussian
open scoped ComplexConjugate

namespace AngularPair.Gaussian

local notation "K" => CyclotomicField 4 ℚ

private theorem angular_ratio (z : ℂ) (hz : z ≠ 0) :
    (z / (‖z‖ : ℂ)) ^ 2 = z / conj z := by
  have hn : (‖z‖ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hz)
  have hc : conj z ≠ 0 := (map_ne_zero _).mpr hz
  have hp : z * conj z = (‖z‖ : ℂ) ^ 2 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, Complex.ofReal_pow]
  field_simp [hn, hc]
  linear_combination hp

/-- Exact finite prime value in the notation Ξ_k((g)) = (g / conjugate g)^(2k).
The archimedean character has the opposite exponent in the idèlic normalization. -/
theorem globalAngularCharacter_power_localValue_RudnickWaxman
    (k : ℤ) (v : HeightOneSpectrum (𝓞 K)) (g : 𝓞 K)
    (hg : v.asIdeal = Ideal.span {g}) :
    (ideleClassNormTwist (globalAngularCharacter ^ k) 0).localValue v =
      (place.embedding (g : K) / conj (place.embedding (g : K))) ^ (-(2 * k)) := by
  rw [globalAngularCharacter_power_localValue k v g hg]
  have hz : place.embedding (g : K) ≠ 0 :=
    (map_ne_zero _).mpr ((map_ne_zero_iff _ (IsFractionRing.injective (𝓞 K) K)).mpr
      (primeGenerator_ne_zero v g hg))
  rw [← angular_ratio _ hz, zpow_neg, zpow_mul, zpow_ofNat]
  rw [← pow_mul, inv_zpow]

end AngularPair.Gaussian

end

section

open Function IsDedekindDomain MeasureTheory NumberField Set
open scoped NNReal NumberField.AdeleRing

namespace AngularPair

set_option quotPrecheck false

attribute [local instance] instIdeleClassMeasurableSpaceSec1 instIdeleClassBorelSpaceSec1
  instIdeleClassT2Sec1 instIdeleClassLocallyCompactSec1 instIdeleClassSecondCountableSec1
  instIdeleClassHaarMeasureSec1

variable {F : Type*} [Field F] [NumberField F]

local notation "G" => IdeleClassGroup (𝓞 F) F
local notation "U" => PontryaginDual G
local notation "N" => ideleClassNorm F
local notation "G₁" => (ideleClassNorm F).ker
local notation "res" => (⟨(ideleClassNorm F).ker.subtype, continuous_subtype_val⟩ : G₁ →ₜ* G)
local notation "tw(" χ "," z ")" => ideleClassNormTwist (F := F) χ z
local notation "D(" χ "," z ")" => MeromorphicOn.divisor (continuedCompletedHeckeL (F := F) χ) univ z
local notation "χs(" τ ")" => {χ : U // ∀ t : ℝ≥0ˣ, χ (τ t) = 1}
local notation "E(" τ "," a ")" => {p : χs(τ) × ℂ // 0 < D(p.1.val,p.2) ∧ a ≤ |p.2.re - 1/2|}
local notation "M(" φ "," c ")" =>
  modulatedFourierMellin (continuousIdeleClassNorm F) univ
    ⟨isProperMap_ideleClassNorm F, ideleClassNorm_ne_one (F := F)⟩
    (ideleClassTamagawaMeasure F) (φ : BruhatCompactSupport G).val c
local notation "term(" φ "," z ")" =>
  (D((z).val.1.val,(z).val.2) : ℂ) * M(φ,tw((z).val.1.val,(z).val.2 - 1/2))

private theorem twistPair_injective (τ : ℝ≥0ˣ →ₜ* G) (hτ : RightInverse τ N) :
    Injective (fun p : χs(τ) × ℂ ↦ tw(p.1.val,p.2)) := by
  rintro ⟨χ,z⟩ ⟨η,w⟩ he
  change tw(χ.val,z) = tw(η.val,w) at he
  have heval (x : χs(τ)) (v : ℂ) (t : ℝ≥0ˣ) :
      tw(x.val,v) (τ t) = (((t : ℝ≥0) : ℝ) : ℂ) ^ v := by
    change (x.val (τ t) : ℂ) * ((((N (τ t)).val : ℝ) : ℂ) ^ v) = _
    rw [x.property, Circle.coe_one, one_mul, hτ]
  have hzw : z = w := (existsUnique_complexPower ((tw(χ.val,z)).comp τ)).unique
    (heval χ z) (fun t ↦ (DFunLike.congr_fun he (τ t)).trans (heval η w t))
  refine Prod.ext (Subtype.ext (ContinuousMonoidHom.ext fun x ↦ Circle.ext ?_)) hzw
  have h := DFunLike.congr_fun he x
  let u : ℂ := (((N x).val : ℝ) : ℂ)
  change (χ.val x : ℂ) * u ^ z = (η.val x : ℂ) * u ^ w at h
  rw [hzw] at h
  exact mul_right_cancel₀ (Complex.cpow_ne_zero_iff.mpr (.inl (Complex.ofReal_ne_zero.mpr
    (NNReal.coe_pos.mpr (Units.zero_lt _)).ne'))) h

private theorem normalized_exterior_site (τ : ℝ≥0ˣ →ₜ* G) (hτ : RightInverse τ N)
    (χ : U) {w : ℂ} (hw : 0 < D(χ,w)) {a : ℝ} (ha : a ≤ |w.re - 1/2|) :
    ∃ q : E(τ,a), tw(χ,w) = tw(q.val.1.val,q.val.2) ∧ D(χ,w) = D(q.val.1.val,q.val.2) := by
  let θ : U := χ.comp (τ.comp (continuousIdeleClassNorm F))
  let ψ : U := χ / θ
  have hψ (t : ℝ≥0ˣ) : ψ (τ t) = 1 := by
    change χ (τ t) / χ (τ (N (τ t))) = 1
    rw [hτ,div_self']
  have hres : χ.comp res = ψ.comp res := ContinuousMonoidHom.ext fun x ↦ by
    change χ x.val = χ x.val / χ (τ (N x.val))
    rw [MonoidHom.mem_ker.mp x.property, map_one, map_one, div_one]
  obtain ⟨δ,hδ⟩ := (spectralZeroMultiplicity_existsUnique_shift_of_restriction_eq χ ψ hres).exists
  let v := (w.re : ℂ) + ((w.im : ℂ) + (δ : ℂ)) * Complex.I
  have he := hδ w.re w.im
  rw [Complex.re_add_im] at he
  have hD : D(χ,w) = D(ψ,v) := by
    have hnat := he.2
    change (meromorphicOrderAt (continuedCompletedHeckeL χ) w).untop₀.toNat =
      (meromorphicOrderAt (continuedCompletedHeckeL ψ) v).untop₀.toNat at hnat
    rw [← MeromorphicOn.divisor_apply (continuedCompletedHeckeL_spec χ).1.meromorphicOn (mem_univ w),
      ← MeromorphicOn.divisor_apply (continuedCompletedHeckeL_spec ψ).1.meromorphicOn (mem_univ v)] at hnat
    omega
  refine ⟨⟨(⟨ψ,hψ⟩,v),hD ▸ hw, ?_⟩, he.1,hD⟩
  simpa [v] using ha

/-- Changing the norm section relabels the exterior zero sites, preserving the abscissa, the
full positive divisor at each zero, and the quasi-character at every common increment. -/
theorem exists_exteriorZeros_chartEquiv (τ υ : ℝ≥0ˣ →ₜ* G)
    (hτ : RightInverse τ N) (hυ : RightInverse υ N) (a : ℝ) :
    ∃ e : E(τ,a) ≃ E(υ,a), ∀ p,
      p.val.2.re = (e p).val.2.re ∧ D(p.val.1.val,p.val.2) = D((e p).val.1.val,(e p).val.2) ∧
        ∀ b : ℂ, tw(p.val.1.val,p.val.2 + b) = tw((e p).val.1.val,(e p).val.2 + b) := by
  classical
  let raw {s : ℝ≥0ˣ →ₜ* G} (p : E(s,a)) := tw(p.val.1.val,p.val.2)
  have hinj {s : ℝ≥0ˣ →ₜ* G} (hs : RightInverse s N) :
      Injective (raw (s := s)) := fun _ _ h ↦ Subtype.ext (twistPair_injective s hs h)
  choose f hf hfo using fun p : E(τ,a) ↦
    normalized_exterior_site υ hυ p.val.1.val p.property.1 p.property.2
  choose g hg hgo using fun q : E(υ,a) ↦
    normalized_exterior_site τ hτ q.val.1.val q.property.1 q.property.2
  let e : E(τ,a) ≃ E(υ,a) :=
    { toFun := f, invFun := g
      left_inv := fun p ↦ hinj hτ ((hg (f p)).symm.trans (hf p).symm)
      right_inv := fun q ↦ hinj hυ ((hf (g q)).symm.trans (hg q).symm) }
  refine ⟨e,fun p ↦ ⟨?_,hfo p,ideleClassNormTwist_add_of_eq (hf p)⟩⟩
  change p.val.2.re = (f p).val.2.re
  simpa only [quasiCharacterAbscissa_ideleClassNormTwist] using
    congrArg (quasiCharacterAbscissa (ideleClassNorm F) (isProperMap_ideleClassNorm F)
      (ideleClassNorm_ne_one (F := F))) (hf p)

/-- Paper: Theorem 12.5.1.1, pp. 519–520. The full-multiplicity exterior series of a
fixed physical test has the same unordered sum in every continuous norm section. A change of
section moves the ordinate and the normalized unitary base character together. -/
theorem hasSum_exteriorZeros_change_section (τ υ : ℝ≥0ˣ →ₜ* G)
    (hτ : RightInverse τ N) (hυ : RightInverse υ N) (φ : BruhatCompactSupport G) (a : ℝ) (L : ℂ) :
    HasSum (fun z : E(τ,a) ↦ term(φ,z)) L ↔ HasSum (fun z : E(υ,a) ↦ term(φ,z)) L := by
  obtain ⟨e,he⟩ := exists_exteriorZeros_chartEquiv τ υ hτ hυ a
  rw [← e.hasSum_iff]
  apply Iff.of_eq
  congr 1
  funext p
  change term(φ,p) = term(φ,e p)
  rw [(he p).2.1, sub_eq_add_neg, sub_eq_add_neg, (he p).2.2]

end AngularPair

end

section

open Classical Function IsDedekindDomain MeasureTheory NumberField Set
open scoped NNReal NumberField.AdeleRing Topology ContDiff

namespace AngularPair

set_option quotPrecheck false
attribute [local instance] instIdeleClassMeasurableSpaceSec1 instIdeleClassBorelSpaceSec1
  instIdeleClassT2Sec1 instIdeleClassLocallyCompactSec1 instIdeleClassSecondCountableSec1
  instIdeleClassHaarMeasureSec1

variable {F : Type*} [Field F] [NumberField F]

local notation "G" => IdeleClassGroup (𝓞 F) F
local notation "U" => PontryaginDual G
local notation "Gψ₁" => (ideleClassNorm F).ker
local notation "μ" => ideleClassTamagawaMeasure F
local notation "V" => (((normOneIdeleClassTamagawaMeasure F) univ).toReal : ℂ)
local notation "ℓ(" x ")" => Real.log ((ideleClassNorm F x : ℝ≥0) : ℝ)
local notation "ord(" χ "," z ")" =>
  MeromorphicOn.divisor (continuedCompletedHeckeL (F := F) χ) univ z
local notation "M(" φ "," χ "," w ")" =>
  modulatedFourierMellin (continuousIdeleClassNorm F) univ
    ⟨isProperMap_ideleClassNorm F, ideleClassNorm_ne_one (F := F)⟩ μ
    (φ : BruhatCompactSupport G).val (ideleClassNormTwist χ w)
local notation "Chars(" τ ")" => {χ : U // ∀ t : ℝ≥0ˣ, χ (τ t) = 1}
local notation "Sites(" τ "," α ")" => {z : Chars(τ) × ℂ //
  0 < ord(z.1.val,z.2) ∧ α ≤ |z.2.re - 1 / 2|}
local notation "Row(" χ "," α ")" => {z : ℂ // 0 < ord(χ,z) ∧ α ≤ |z.re - 1 / 2|}
local notation "K(" g "," w ")" => ∫ x : ℝ, (g : ℝ → ℂ) x * Complex.exp (w * (x : ℂ))

private theorem mellin_row (τ : ℝ≥0ˣ →ₜ* G) (hτ : RightInverse τ (ideleClassNorm F))
    (ψ χ : Chars(τ)) (g : ℝ → ℂ) (hg : ContDiff ℝ (∞) g) (hc : HasCompactSupport g)
    (φ : BruhatCompactSupport G) (hφ : ∀ x, φ.val x = (ψ.val⁻¹ x : ℂ) * g ℓ(x)) (w : ℂ) :
    M(φ,χ.val,w) = if χ = ψ then V * K(g,w) else 0 := by
  obtain ⟨φ₀, h₀⟩ := exists_normTest (F := F) g hg hc
  have he : M(φ,χ.val,w) = M(φ₀,χ.val * ψ.val⁻¹,w) := by
    simp only [modulatedFourierMellin, relativeVerticalStrip, preimage_univ, indicator_univ]
    apply integral_congr_ae
    filter_upwards with x
    let q : ℂ := ((((ideleClassNorm F x).val : ℝ) : ℂ) ^ w)
    change φ.val x * ((χ.val x : ℂ) * q) = φ₀.val x * (((χ.val * ψ.val⁻¹) x : ℂ) * q)
    rw [hφ, h₀]
    change _ = _ * (((χ.val x * ψ.val⁻¹ x : Circle) : ℂ) * _)
    rw [Circle.coe_mul]
    ring
  rw [he, normTest_mellin g hg.continuous φ₀ h₀]
  by_cases eq : χ = ψ
  · subst χ
    have hchar : ψ.val * ψ.val⁻¹ = 1 := mul_inv_cancel _
    rw [ite_eq_left rfl, hchar, ite_eq_left (by intro u; rfl)]
    congr 1
    have h := grh_shift_integral g hg.continuous (fun _ : ℝ≥0ˣ ↦ (1 : ℂ)) (fun _ ↦ rfl) 0 w
    simpa using h
  · rw [ite_eq_right eq, ite_eq_right, zero_mul]
    intro h
    apply eq
    apply Subtype.ext
    apply ContinuousMonoidHom.ext
    intro x
    let u := (τ (ideleClassNorm F x))⁻¹ * x
    have hu : u ∈ Gψ₁ := by simp [u, MonoidHom.mem_ker, hτ _]
    have hval := h ⟨u,hu⟩
    change χ.val u * (ψ.val u)⁻¹ = 1 at hval
    have key (p : Chars(τ)) : p.val x = p.val u := by
      rw [show u = (τ (ideleClassNorm F x))⁻¹ * x from rfl, map_mul, map_inv, p.property,
        inv_one, one_mul]
    exact (key χ).trans ((mul_inv_eq_one.mp hval).trans (key ψ).symm)

private theorem row_summable (χ : U) (φ : BruhatCompactSupport G) (α : ℝ) :
    Summable (fun z : Row(χ,α) ↦ (ord(χ,z.val) : ℂ) * M(φ,χ,z.val - 1/2)) := by
  let e (z : Row(χ,α)) : {s : ℂ // 0 < ord(χ,s)} := ⟨z.val,z.property.1⟩
  have hi : Injective e := fun x y h ↦ Subtype.ext (congrArg Subtype.val h : (e x).val = (e y).val)
  have h := (idelicExplicitFormula_summable_spectral_fiber φ χ).of_norm.comp_injective hi
  apply h.congr
  intro z
  change (ord(χ,z.val) : ℂ) * _ = _
  congr 1
  rw [show M(φ,χ,z.val - 1/2) = ∫ g, φ.val g * ideleClassNormTwist χ (z.val - 1/2) g ∂μ
    from Set.indicator_of_mem (Set.mem_univ _) _]
  apply integral_congr_ae
  filter_upwards with x
  let N : ℂ := ((ideleClassNorm F x).val : ℝ)
  have hN : N ≠ 0 := Complex.ofReal_ne_zero.mpr (NNReal.coe_pos.mpr (Units.zero_lt _)).ne'
  change φ.val x * ((χ x : ℂ) * N ^ z.val) * N ^ (-1 / 2 : ℂ) =
    φ.val x * ((χ x : ℂ) * N ^ (z.val - 1 / 2))
  rw [show z.val - 1/2 = z.val + (-1/2) by ring, Complex.cpow_add _ _ hN]
  ring


private theorem separated_hasSum (τ : ℝ≥0ˣ →ₜ* G) (hτ : RightInverse τ (ideleClassNorm F))
    (ψ : Chars(τ)) (g : ℝ → ℂ) (hg : ContDiff ℝ (∞) g) (hc : HasCompactSupport g)
    (φ : BruhatCompactSupport G) (hφ : ∀ x, φ.val x = (ψ.val⁻¹ x : ℂ) * g ℓ(x)) (α : ℝ) :
    HasSum (fun z : Sites(τ,α) ↦ (ord(z.val.1.val,z.val.2) : ℂ) *
      M(φ,z.val.1.val,z.val.2 - 1/2))
      (∑' w : ℂ, {z : ℂ | 0 < ord(ψ.val,z) ∧ α ≤ |z.re - 1/2|}.indicator
        (fun z ↦ (ord(ψ.val,z) : ℂ) * (V * K(g,z - 1/2))) w) := by
  let E : Set ℂ := {z : ℂ | 0 < ord(ψ.val,z) ∧ α ≤ |z.re - 1/2|}
  let A (z : ℂ) := (ord(ψ.val,z) : ℂ) * (V * K(g,z - 1/2))
  let e (z : E) : Sites(τ,α) := ⟨(ψ,z.val),z.property⟩
  have hi : Injective e := fun x y h ↦ Subtype.ext (congrArg (fun z : Sites(τ,α) ↦ z.val.2) h)
  have hs : Summable (fun z : E ↦ A z.val) := (row_summable ψ.val φ α).congr fun z ↦ by
    simp [A, mellin_row τ hτ ψ ψ g hg hc φ hφ]
  change HasSum _ (∑' z : ℂ, E.indicator A z)
  rw [← tsum_subtype E A]
  apply (hi.hasSum_iff ?_).mp
  · apply hs.hasSum.congr_fun
    intro z
    change (ord(ψ.val,z.val) : ℂ) * M(φ,ψ.val,z.val - 1/2) = A z.val
    simp [A, mellin_row τ hτ ψ ψ g hg hc φ hφ]
  · intro z hz
    have hne : z.val.1 ≠ ψ := by
      intro he
      apply hz
      refine ⟨⟨z.val.2, ?_⟩, Subtype.ext (Prod.ext he.symm rfl)⟩
      change 0 < ord(ψ.val,z.val.2) ∧ α ≤ _
      simpa only [← he] using z.property
    rw [mellin_row τ hτ ψ _ g hg hc φ hφ, ite_eq_right hne, mul_zero]

private theorem mellin_sub (φ φ₁ φ₂ : BruhatCompactSupport G)
    (h : ∀ x, φ.val x = φ₁.val x - φ₂.val x) (χ : U) (w : ℂ) :
    M(φ,χ,w) = M(φ₁,χ,w) - M(φ₂,χ,w) := by
  let c := ideleClassNormTwist χ w
  have hint (f : BruhatCompactSupport G) : Integrable (fun x ↦ f.val x * c x) μ :=
    ((continuous_of_bruhatSmooth ((mem_bruhatSmoothSubmodule_iff _).mp f.property.1)).mul
      c.continuous).integrable_of_hasCompactSupport f.property.2.mul_right
  simp only [modulatedFourierMellin, relativeVerticalStrip, preimage_univ, indicator_univ]
  rw [← integral_sub (hint φ₁) (hint φ₂)]
  apply integral_congr_ae
  filter_upwards with x
  rw [h, sub_mul]

/-- Two normalized character rows with identical positive exterior multiplicities cancel at the
same raw zero for the difference of their physical compact tests. The edges are included. -/
theorem hasSum_exteriorZeros_characterPair (τ : ℝ≥0ˣ →ₜ* G) (hτ : RightInverse τ (ideleClassNorm F))
    (ψ η : Chars(τ)) (g : ℝ → ℂ) (hg : ContDiff ℝ (∞) g) (hc : HasCompactSupport g) (α : ℝ)
    (hord : ∀ z : ℂ, α ≤ |z.re - 1/2| → (0 < ord(ψ.val,z) ∨ 0 < ord(η.val,z)) →
      ord(ψ.val,z) = ord(η.val,z))
    (φ : BruhatCompactSupport G) (hφ : ∀ x, φ.val x = ((ψ.val⁻¹ x : ℂ) - (η.val⁻¹ x : ℂ)) * g ℓ(x)) :
    HasSum (fun z : Sites(τ,α) ↦ (ord(z.val.1.val,z.val.2) : ℂ) *
      M(φ,z.val.1.val,z.val.2 - 1/2)) 0 := by
  obtain ⟨φ₁,h₁⟩ := exists_characterNormTest (F := F) ψ.val⁻¹ g hg hc
  obtain ⟨φ₂,h₂⟩ := exists_characterNormTest (F := F) η.val⁻¹ g hg hc
  have hp (x : G) : φ.val x = φ₁.val x - φ₂.val x := by rw [hφ,h₁,h₂,sub_mul]
  have hs := (separated_hasSum τ hτ ψ g hg hc φ₁ h₁ α).sub (separated_hasSum τ hτ η g hg hc φ₂ h₂ α)
  have he : (fun w : ℂ ↦ {z : ℂ | 0 < ord(ψ.val,z) ∧ α ≤ |z.re - 1/2|}.indicator
        (fun z ↦ (ord(ψ.val,z) : ℂ) * (V * K(g,z - 1/2))) w) =
      fun w : ℂ ↦ {z : ℂ | 0 < ord(η.val,z) ∧ α ≤ |z.re - 1/2|}.indicator
        (fun z ↦ (ord(η.val,z) : ℂ) * (V * K(g,z - 1/2))) w := by
    funext z
    by_cases hw : α ≤ |z.re - 1/2|
    · by_cases hd : 0 < ord(ψ.val,z) ∨ 0 < ord(η.val,z)
      · simp [Set.indicator, hord z hw hd]
      · have hn (T : ℤ) (hT : ¬ 0 < T) : ¬ (0 < T ∧ α ≤ |z.re - 1/2|) := fun h ↦ hT h.1
        rw [Set.indicator_of_notMem (hn _ (fun h ↦ hd (Or.inl h))),
          Set.indicator_of_notMem (hn _ (fun h ↦ hd (Or.inr h)))]
    · have hn (T : ℤ) : ¬ (0 < T ∧ α ≤ |z.re - 1/2|) := fun h ↦ hw h.2
      rw [Set.indicator_of_notMem (hn (ord(ψ.val,z))), Set.indicator_of_notMem (hn (ord(η.val,z)))]
  have he' := congrArg (fun f : ℂ → ℂ ↦ ∑' z, f z) he
  rw [he',sub_self] at hs
  apply hs.congr_fun
  intro z
  rw [mellin_sub φ φ₁ φ₂ hp, mul_sub]



private theorem volume_ne_zero : V ≠ 0 := by
  rw [normOneIdeleClassTamagawaMeasure_volume]
  have := NumberField.Units.regulator_pos F
  have := NumberField.classNumber_pos F
  have := NumberField.Units.torsionOrder_pos F
  have := Int.natAbs_pos.mpr (NumberField.discr_ne_zero F)
  exact Complex.ofReal_ne_zero.mpr (ENNReal.toReal_ne_zero.mpr
    ⟨(ENNReal.ofReal_pos.mpr (by positivity)).ne', ENNReal.ofReal_ne_top⟩)

private theorem mellin_normalizedPair (τ : ℝ≥0ˣ →ₜ* G) (hτ : RightInverse τ (ideleClassNorm F))
    (ψ η χ : Chars(τ)) (g : ℝ → ℂ) (hg : ContDiff ℝ (∞) g) (hc : HasCompactSupport g)
    (φ : BruhatCompactSupport G)
    (hφ : ∀ x, φ.val x = ((ψ.val⁻¹ x : ℂ) - (η.val⁻¹ x : ℂ)) * g ℓ(x) / V) (w : ℂ) :
    M(φ,χ.val,w) = (if χ = ψ then K(g,w) else 0) - (if χ = η then K(g,w) else 0) := by
  let q (x : ℝ) := g x / V
  have hq : ContDiff ℝ (∞) q := hg.div_const _
  have hqc : HasCompactSupport q := HasCompactSupport.intro hc.isCompact fun x hx ↦ by
    change g x / V = 0
    rw [image_eq_zero_of_notMem_tsupport hx, zero_div]
  obtain ⟨φ₁,h₁⟩ := exists_characterNormTest (F := F) ψ.val⁻¹ q hq hqc
  obtain ⟨φ₂,h₂⟩ := exists_characterNormTest (F := F) η.val⁻¹ q hq hqc
  have hp (x : G) : φ.val x = φ₁.val x - φ₂.val x := by rw [hφ,h₁,h₂]; dsimp [q]; ring
  have hi : K(q,w) = K(g,w) / V := by
    rw [← integral_div]
    congr 1; funext x; dsimp [q]; ring
  have hV : V ≠ 0 := volume_ne_zero
  rw [mellin_sub φ φ₁ φ₂ hp, mellin_row τ hτ ψ χ q hq hqc φ₁ h₁,
    mellin_row τ hτ η χ q hq hqc φ₂ h₂, hi, mul_div_cancel₀ _ hV]


end AngularPair

end

section

open Classical Function IsDedekindDomain MeasureTheory NumberField Set
open scoped NNReal NumberField.AdeleRing Topology ContDiff ComplexConjugate

namespace AngularPair

set_option quotPrecheck false
attribute [local instance] instIdeleClassMeasurableSpaceSec1 instIdeleClassBorelSpaceSec1
  instIdeleClassT2Sec1 instIdeleClassLocallyCompactSec1 instIdeleClassSecondCountableSec1
  instIdeleClassHaarMeasureSec1

local notation "F₄" => CyclotomicField 4 ℚ
local notation "G₄" => IdeleClassGroup (𝓞 F₄) F₄
local notation "A₄" => Gaussian.globalAngularCharacter
local notation "N₄" => ideleClassNorm F₄
local notation "V₄" => (((normOneIdeleClassTamagawaMeasure F₄) univ).toReal : ℂ)
local notation "M₄(" φ "," χ "," w ")" =>
  modulatedFourierMellin (continuousIdeleClassNorm F₄) univ
    ⟨isProperMap_ideleClassNorm F₄, ideleClassNorm_ne_one (F := F₄)⟩ (ideleClassTamagawaMeasure F₄)
    (φ : BruhatCompactSupport G₄).val (ideleClassNormTwist χ w)
local notation "D₄(" χ "," z ")" => MeromorphicOn.divisor (continuedCompletedHeckeL (F := F₄) χ) univ z
local notation "χ₄(" τ ")" => {χ : PontryaginDual G₄ // ∀ t : ℝ≥0ˣ, χ (τ t) = 1}
local notation "E₄(" τ "," α ")" => {z : χ₄(τ) × ℂ //
  0 < D₄(z.1.val,z.2) ∧ α ≤ |z.2.re - 1/2|}

/-- Rudnick and Waxman, *Angles of Gaussian primes*, §4.1, p. 13.
The native completed Gaussian Hecke functions indexed by opposite angular powers are
equal at the same complex argument, with their full zero and pole orders. -/
theorem gaussianAngular_completedHeckeL_inv (k : ℤ) :
    continuedCompletedHeckeL (A₄^k) = continuedCompletedHeckeL (A₄^k)⁻¹ :=
  continuedCompletedHeckeL_eq_of_gamma_and_finite _ _
    (fun s ↦ Gaussian.globalAngularCharacter_power_gammaFactor_inv k s.val)
    (finiteHeckeL_eq_of_eulerPermutation _ _ Gaussian.conjugatePrime
      (fun v s ↦ Gaussian.globalAngularCharacter_power_eulerFactor k v s.val))

/-- Paper: Theorem 12.5.1.1, pp. 519–520. A single real odd radial profile gives,
for each nonzero angular degree, a nonzero inversion-even Gaussian idèle-class test.
Its two Mellin rows have opposite calibrated coefficients at the same raw site and
its signed exterior sum is zero in every norm section, with the full edge orders. -/
theorem exists_gaussianAngularPair_exteriorZeros :
    ∃ g : ℝ → ℂ, ContDiff ℝ (∞) g ∧ HasCompactSupport g ∧ Function.Odd g ∧
      (∀ x, conj (g x) = g x) ∧
      (∀ w, bilateralLaplace g w = GaussianPairDetector.oddRadialMultiplier w) ∧
      ∀ (k : ℤ), k ≠ 0 → ∃ φ : BruhatCompactSupport G₄,
        (∀ x, φ.val x = (((A₄^k)⁻¹ x : ℂ) - ((A₄^k) x : ℂ)) *
          g (logIdeleClassNorm F₄ x) / V₄) ∧
        (∀ x, φ.val x⁻¹ = φ.val x) ∧ (∀ u : (N₄).ker, φ.val u.val = 0) ∧ (∃ x, φ.val x ≠ 0) ∧
        (∀ w, M₄(φ,A₄^k,w) = GaussianPairDetector.oddRadialMultiplier w ∧
          M₄(φ,(A₄^k)⁻¹,w) = -GaussianPairDetector.oddRadialMultiplier w) ∧
        (∀ χ : PontryaginDual G₄, (∀ t, χ (QuotientGroup.mk (canonicalIdeleNormSection F₄ t)) = 1) →
          χ ≠ A₄^k → χ ≠ (A₄^k)⁻¹ → ∀ w, M₄(φ,χ,w) = 0) ∧
        ∀ (τ : ℝ≥0ˣ →ₜ* G₄), RightInverse τ N₄ → ∀ α : ℝ,
          HasSum (fun z : E₄(τ,α) ↦ (D₄(z.val.1.val,z.val.2) : ℂ) *
            M₄(φ,z.val.1.val,z.val.2 - 1/2)) 0 := by
  obtain ⟨g, hg, hc, ho, _, hr, hn, hL⟩ := GaussianPairDetector.exists_oddRadialDetector
  refine ⟨g, hg, hc, ho, hr, hL, fun k hk ↦ ?_⟩
  let σ : ℝ≥0ˣ →ₜ* G₄ := ⟨(QuotientGroup.mk' _).comp (canonicalIdeleNormSection F₄),
    continuous_quotient_mk'.comp (canonicalIdeleNormSection_continuous _)⟩
  have hσ : RightInverse σ N₄ := canonicalIdeleNormSection_rightInverse _
  have hak (t : ℝ≥0ˣ) : (A₄^k) (σ t) = 1 := by
    have ev : (A₄ ^ k) (σ t) = (A₄ (σ t))^k := by
      let e : PontryaginDual G₄ →* Circle := ⟨⟨fun χ ↦ χ (σ t),rfl⟩,fun _ _ ↦ rfl⟩
      exact e.map_zpow A₄ k
    rw [ev, show A₄ (σ t) = 1 from Gaussian.globalAngularCharacter_normSection t, one_zpow]
  let ψ : χ₄(σ) := ⟨A₄^k,hak⟩
  let η : χ₄(σ) := ⟨(A₄^k)⁻¹,fun t ↦ by change ((A₄^k) (σ t))⁻¹ = 1; rw [hak,inv_one]⟩
  have hchars : A₄^k ≠ (A₄^k)⁻¹ := by
    intro he
    have h := Gaussian.globalAngularCharacter_power_injective
      (show A₄^k = A₄^(-k) by simpa only [zpow_neg] using he)
    omega
  have hne : ψ ≠ η := fun h ↦ hchars (congrArg Subtype.val h)
  obtain ⟨φ,hφ,he,hvan,hNZ⟩ := GaussianPairDetector.exists_inversionEven_characterPairTest
    σ hσ _ hak hchars hg hc ho hn (volume_ne_zero (F := F₄))
  have hp (x : G₄) : φ.val x = ((ψ.val⁻¹ x : ℂ) - (η.val⁻¹ x : ℂ)) *
      g (Real.log ((N₄ x : ℝ≥0) : ℝ)) / V₄ := by
    simpa only [ψ,η,inv_inv] using hφ x
  refine ⟨φ,hφ,he,hvan,hNZ,fun w ↦ ?_,fun χ hχ h₁ h₂ w ↦ ?_,fun τ hτ α ↦ ?_⟩
  · have h₁ := mellin_normalizedPair σ hσ ψ η ψ g hg hc φ hp w
    have h₂ := mellin_normalizedPair σ hσ ψ η η g hg hc φ hp w
    change (M₄(φ,ψ.val,w) = _) ∧ (M₄(φ,η.val,w) = _)
    rw [h₁,h₂,ite_eq_left rfl,ite_eq_right hne,ite_eq_right (Ne.symm hne),
      sub_zero,zero_sub,show (∫ x : ℝ, g x * Complex.exp (w * (x:ℂ))) = _ from hL w]
    simp
  · let θ : χ₄(σ) := ⟨χ,hχ⟩
    change M₄(φ,θ.val,w) = 0
    rw [mellin_normalizedPair σ hσ ψ η θ g hg hc φ hp, ite_eq_right (fun h ↦ h₁ (congrArg Subtype.val h)),
      ite_eq_right (fun h ↦ h₂ (congrArg Subtype.val h)),sub_zero]
  · apply (hasSum_exteriorZeros_change_section σ τ hσ hτ φ α 0).mp
    let q (x : ℝ) := g x / V₄
    have hqc : HasCompactSupport q := HasCompactSupport.intro hc.isCompact fun x hx ↦ by
      change g x / V₄ = 0
      rw [image_eq_zero_of_notMem_tsupport hx,zero_div]
    apply hasSum_exteriorZeros_characterPair σ hσ ψ η q (hg.div_const _) hqc α
    · intro z _ _
      exact congrArg (fun L : ℂ → ℂ ↦ MeromorphicOn.divisor L univ z) (gaussianAngular_completedHeckeL_inv k)
    · intro x
      change φ.val x = (((A₄^k)⁻¹ x : ℂ) - (((A₄^k)⁻¹)⁻¹ x : ℂ)) * (g _ / V₄)
      rw [hφ,inv_inv]
      ring

end AngularPair
end

/-- At fixed strip and input operator, it suffices to test a single prescribed nonempty
open set of log norms. -/
theorem stripTestAction_projectiveKernel_iff_support_in_open {α s : ℝ} (ha : 0 ≤ α) (hs : 0 ≤ s)
    (P : W(α, s) →L[ℂ] W(α, s)) {U : Set ℝ} (ho : IsOpen U) (hne : U.Nonempty) :
    (∀ φ : BruhatCompactSupport C𝔽, kerExists(ha, hs, P, φ)) ↔
      ∀ φ : BruhatCompactSupport C𝔽, tsupport φ.val ⊆ ℓ ⁻¹' U → kerExists(ha, hs, P, φ) := by
  refine ⟨fun h φ _ ↦ h φ, ?_⟩
  intro h φ
  obtain ⟨S, f, ψ, g, hsum, hsup, htr⟩ := bruhatCompactSupport_finite_sum_translates_of_logNorm ho hne φ
  rw [hsum]
  exact kernelLocalization_sum ha hs P f fun i ↦
    (stripTestAction_projectiveKernel_translate_iff ha hs P (g i) (ψ i) (f i) (htr i)).mpr (h _ (hsup i))

/-- Paper: (12.5.1.4), p. 520. The kernel assertion for all tests vanishing on the
norm-one classes is equivalent to testing any nonempty open set of log norms. In
particular a fixed short interval, or an arbitrary far half-line, suffices. -/
theorem exists_projectiveKernel_stripTestAction_spectralProjection_iff_support_in_open
    {α s : ℝ} (hα : 0 < α) (hs : 3 ≤ s) {U : Set ℝ} (ho : IsOpen U) (hne : U.Nonempty) :
    let hs' : 0 ≤ s := (by norm_num : (0 : ℝ) ≤ 3).trans hs
    let P := spectralProjection (F := F) (1 / 2) hα.le hs'
    (∀ φ : BruhatCompactSupport C𝔽, (∀ g : C₁, φ.val g = 0) → kerExists(hα.le, hs', P, φ)) ↔
      ∀ φ : BruhatCompactSupport C𝔽, tsupport φ.val ⊆ ℓ ⁻¹' U → kerExists(hα.le, hs', P, φ) := by
  intro hs' P
  apply Iff.trans _ (stripTestAction_projectiveKernel_iff_support_in_open hα.le hs' P ho hne)
  refine ⟨fun h ↦ ?_, fun h φ _ ↦ h φ⟩
  apply (stripTestAction_projectiveKernel_iff_support_in_open hα.le hs' P isOpen_Ioi
    (nonempty_Ioi : (Ioi (0 : ℝ)).Nonempty)).mpr
  intro φ hφ
  apply h φ
  intro g
  apply image_eq_zero_of_notMem_tsupport
  intro hg
  have hx : 0 < ℓ g.val := hφ hg
  change 0 < Real.log ((ideleClassNorm F g.val).val : ℝ) at hx
  rw [g.property] at hx
  simp at hx

end KernelLocalization

end RiemannMasullo.Isolated

namespace RiemannMasullo.Isolated.AngularPair

/-- De Smit, *Generating arithmetically equivalent number fields with elliptic curves*,
§3, pp. 395–396. For the curve `y² = x³ - x + 1`, the quartic division coordinate
and its radicand generate the same field in characteristic zero, by the second identity. -/
theorem deSmit_quartic_coordinates {K : Type*} [Field K] (x : K)
    (hx : 3 * x ^ 4 - 6 * x ^ 2 + 12 * x - 1 = 0) :
    let D := x ^ 3 - x + 1
    27 * D ^ 4 + 216 * D ^ 3 + 414 * D ^ 2 - 529 = 0 ∧
      92 * x = -3 * (3 * D ^ 3 + 24 * D ^ 2 + 23 * D - 46) := by
  dsimp only
  constructor
  · linear_combination
      (9 * x ^ 8 - 18 * x ^ 6 + 72 * x ^ 5 + 21 * x ^ 4 - 108 * x ^ 3 + 120 * x ^ 2 + 48 * x - 128) * hx
  · linear_combination (3 * x ^ 5 - 3 * x ^ 3 + 21 * x ^ 2 + 4 * x - 12) * hx

/-- The induced traces of the line and quotient signs agree for every matrix of
`GL₂(𝔽₃)`. In the chart `(1,t)`, a fixed line has eigenvalue `a+b*t` and quotient
eigenvalue `d-b*t`. The line `(0,1)` supplies the remaining summand. -/
theorem glTwoThree_diagonal_induced_traces (a b c d : ZMod 3) (hinv : a * d - b * c ≠ 0) :
    let sign (z : ZMod 3) : ℤ := if z = 1 then 1 else -1
    (if b = 0 then sign d else 0) +
        (∑ t : ZMod 3, if c + d * t = t * (a + b * t) then sign (a + b * t) else 0) =
      (if b = 0 then sign a else 0) +
        (∑ t : ZMod 3, if c + d * t = t * (a + b * t) then sign (d - b * t) else 0) := by
  decide +revert

/-- The residue of the division coordinate at the degree-one prime above 41 is a simple
root. The two quadratic radicands have opposite square classes at that prime. -/
theorem deSmit_separating_prime :
    let x : ZMod 41 := 24
    let D := x ^ 3 - x + 1
    3 * x ^ 4 - 6 * x ^ 2 + 12 * x - 1 = 0 ∧ 12 * x ^ 3 - 12 * x + 12 ≠ 0 ∧
      D ≠ 0 ∧ (∃ y : ZMod 41, y ^ 2 = D) ∧ ∀ y : ZMod 41, y ^ 2 ≠ -3 * D := by
  decide

section

open Classical ComplexConjugate Function MeasureTheory NumberField Set
open scoped ContDiff NNReal

private theorem translatedMultiplier_neg (z : ℂ) :
    translatedIntervalMultiplier quadraticBoxLaplace (-z) =
      -Complex.exp (-6 * z) * translatedIntervalMultiplier quadraticBoxLaplace z := by
  have he : Complex.exp (-6 * z) * Complex.exp (3 * z) = Complex.exp (-(3 * z)) := by
    rw [← Complex.exp_add]
    congr 1
    ring
  unfold translatedIntervalMultiplier
  rw [GaussianPairDetector.quadratic_even, show (3 : ℂ) * -z = -(3 * z) by ring, ← he]
  ring

/-- One real even compact smooth radial test vanishes at the origin and detects the whole
off-axis open strip. It is the sum of a translated three-moment profile and its reflection. -/
theorem exists_evenRadialDetector :
    ∃ g : ℝ → ℂ, ContDiff ℝ ∞ g ∧ HasCompactSupport g ∧ Function.Even g ∧
      (∀ x, conj (g x) = g x) ∧ g 0 = 0 ∧
      (∀ w : ℂ, 0 < |w.re| → |w.re| < 1 / 2 → bilateralLaplace g w ≠ 0) ∧
      bilateralLaplace g (-(1 / 2)) = 0 ∧ bilateralLaplace g 0 = 0 ∧
      bilateralLaplace g (1 / 2) = 0 := by
  obtain ⟨H, hH, hs, hsup, hp, hn, _⟩ := exists_translatedGevreyPolarProfile
  let f (x : ℝ) : ℂ := H x
  let g (x : ℝ) : ℂ := f x + f (-x)
  have hf : ContDiff ℝ ∞ f := Complex.ofRealCLM.contDiff.comp hs
  have hHc : HasCompactSupport H := isCompact_Icc.of_isClosed_subset (isClosed_tsupport _) hsup
  have hc : HasCompactSupport f := hHc.comp_left (g := Complex.ofReal) rfl
  have hcr : HasCompactSupport (fun x : ℝ ↦ f (-x)) := hc.comp_homeomorph (Homeomorph.neg ℝ)
  have hL (w : ℂ) : bilateralLaplace g w = bilateralLaplace f w + bilateralLaplace f (-w) := by
    rw [← GaussianPairDetector.laplace_reflect f w]
    unfold bilateralLaplace
    rw [← integral_add (GaussianPairDetector.tilted_smooth_integrable hf.continuous hc w)
      (GaussianPairDetector.tilted_smooth_integrable (f := fun x ↦ f (-x))
        (hf.continuous.comp continuous_neg) hcr w)]
    congr 1
    funext x
    exact add_mul _ _ _
  have hz : H 0 = 0 := image_eq_zero_of_notMem_tsupport fun h ↦ by
    have := (hsup h).1
    norm_num at this
  refine ⟨g, hf.add (hf.comp contDiff_id.neg), hc.add hcr, fun x ↦ ?_, fun x ↦ ?_,
    ?_, fun w hw hb ↦ ?_, ?_, ?_, ?_⟩
  · simp [g, add_comm]
  · simp [g, f]
  · simp [g, f, hz]
  · have hu : Complex.exp (-6 * w) ≠ 1 := by
      intro he
      have t := congrArg (fun u : ℂ ↦ ‖u‖) he
      rw [Complex.norm_exp, norm_one, ← Real.exp_zero, Real.exp_eq_exp] at t
      have := abs_pos.mp hw
      simp [Complex.mul_re] at t
      exact this (by linarith)
    have hm : translatedIntervalMultiplier quadraticBoxLaplace w ≠ 0 := by
      rw [← hH]
      exact hn w hw hb
    rw [hL, show bilateralLaplace f = translatedIntervalMultiplier quadraticBoxLaplace from hH,
      translatedMultiplier_neg]
    convert mul_ne_zero (sub_ne_zero.mpr (Ne.symm hu)) hm using 1
    ring
  · rw [hL, neg_neg, show bilateralLaplace f (-(1/2)) = 0 from hp.1,
      show bilateralLaplace f (1/2) = 0 from hp.2.2, add_zero]
  · rw [hL, neg_zero, show bilateralLaplace f 0 = 0 from hp.2.1, add_zero]
  · rw [hL, show bilateralLaplace f (1/2) = 0 from hp.2.2,
      show bilateralLaplace f (-(1/2)) = 0 from hp.1, add_zero]

end

section

open Classical ComplexConjugate Function MeasureTheory NumberField Set
open scoped ContDiff NNReal

open Filter
open scoped Topology

set_option quotPrecheck false

attribute [local instance] instIdeleClassMeasurableSpaceSec1 instIdeleClassBorelSpaceSec1
  instIdeleClassT2Sec1 instIdeleClassLocallyCompactSec1 instIdeleClassSecondCountableSec1
  instIdeleClassHaarMeasureSec1

variable {F : Type*} [Field F] [NumberField F]

local notation "G" => IdeleClassGroup (𝓞 F) F
local notation "U" => PontryaginDual G
local notation "N" => ideleClassNorm F
local notation "V" => (((normOneIdeleClassTamagawaMeasure F) univ).toReal : ℂ)
local notation "D(" χ "," w ")" => MeromorphicOn.divisor (continuedCompletedHeckeL (F := F) χ) univ w
local notation "M(" φ "," χ "," w ")" =>
  modulatedFourierMellin (continuousIdeleClassNorm F) univ
    ⟨isProperMap_ideleClassNorm F, ideleClassNorm_ne_one (F := F)⟩ (ideleClassTamagawaMeasure F)
    (φ : BruhatCompactSupport G).val (ideleClassNormTwist χ w)
local notation "Chars(" τ ")" => {χ : U // ∀ t : ℝ≥0ˣ, χ (τ t) = 1}
local notation "Sites(" τ "," α ")" => {z : Chars(τ) × ℂ //
  0 < D(z.1.val,z.2) ∧ α ≤ |z.2.re - 1 / 2|}

private theorem quadratic_on_section (χ : U) (hχ : χ ^ 2 = 1)
    (τ : ℝ≥0ˣ →ₜ* G) (t : ℝ≥0ˣ) : χ (τ t) = 1 := by
  let r := Units.mk0 (NNReal.sqrt t.val) (by
    exact (NNReal.sqrt_pos.mpr (Units.zero_lt t)).ne')
  have hr : r ^ 2 = t := Units.ext (NNReal.sq_sqrt t.val)
  rw [← hr, map_pow, map_pow]
  exact congrArg (fun θ : U ↦ θ (τ r)) hχ

private theorem quadratic_inv (χ : U) (hχ : χ ^ 2 = 1) : χ⁻¹ = χ := by
  calc χ⁻¹ = χ⁻¹ * 1 := (mul_one _).symm
       _ = χ := by rw [← hχ, pow_two, inv_mul_cancel_left]

private theorem quadratic_values_real (χ : U) (hχ : χ ^ 2 = 1) (x : G) :
    conj (χ x : ℂ) = (χ x : ℂ) := by
  have h := congrArg (fun θ : U ↦ (θ x : ℂ)) (quadratic_inv χ hχ)
  change ((χ x)⁻¹ : Circle).val = (χ x : ℂ) at h
  exact (Circle.coe_inv_eq_conj (χ x)).symm.trans h

private theorem dual_completed_order (χ : U) (z : ℂ) :
    meromorphicOrderAt (continuedCompletedHeckeL χ⁻¹) (1 - z) =
      meromorphicOrderAt (continuedCompletedHeckeL χ) z := by
  obtain ⟨hχ, heχ⟩ := continuedCompletedHeckeL_spec χ
  obtain ⟨hη, heη⟩ := continuedCompletedHeckeL_spec χ⁻¹
  obtain ⟨ε, hε, hn, hfe⟩ := completedHeckeL_continuation_functionalEquation χ _ _ hχ heχ hη heη
  have hc : meromorphicOrderAt (fun s ↦ continuedCompletedHeckeL χ⁻¹ (1 - s)) z =
      meromorphicOrderAt (continuedCompletedHeckeL χ⁻¹) (1 - z) := by
    simpa [Function.comp_def] using
      meromorphicOrderAt_comp_of_deriv_ne_zero (f := continuedCompletedHeckeL χ⁻¹)
        (show AnalyticAt ℂ (fun s : ℂ ↦ 1 - s) z by fun_prop)
        (show deriv (fun s : ℂ ↦ 1 - s) z ≠ 0 by simp)
  rw [show (fun s ↦ continuedCompletedHeckeL χ⁻¹ (1 - s)) = ε * continuedCompletedHeckeL χ
    from funext hfe, meromorphicOrderAt_mul_of_ne_zero (hε.analyticAt z) (hn z)] at hc
  exact hc.symm

private theorem positive_divisor_re_pos (χ : U) (z : ℂ) (h : 0 < D(χ,z)) : 0 < z.re := by
  by_contra! hs
  have hraw : 0 < meromorphicOrderAt (continuedCompletedHeckeL χ) z := by
    rw [MeromorphicOn.divisor_apply (continuedCompletedHeckeL_spec χ).1.meromorphicOn (mem_univ _)] at h
    cases hh : meromorphicOrderAt (continuedCompletedHeckeL χ) z with
    | top => simp
    | coe k =>
      rw [hh, WithTop.untop₀_coe] at h
      exact_mod_cast h
  have hdual : 0 < meromorphicOrderAt (continuedCompletedHeckeL χ⁻¹) (1 - z) := by
    rwa [dual_completed_order]
  have hpos : 0 < (1 - z).re := by rw [Complex.sub_re, Complex.one_re]; linarith
  obtain ⟨hm, he⟩ := continuedCompletedHeckeL_spec χ⁻¹
  have hu := completedHeckeL_continuation_zeros χ⁻¹ _ hm he hpos hdual
  rw [Complex.sub_re, Complex.one_re] at hu
  linarith

/-- Equality of ordinary finite Hecke series on the Euler half-plane identifies every
positive completed order, including those on a proposed strip edge. -/
theorem positive_completed_divisors_eq_of_finiteHeckeL_eq (ψ η : U)
    (heq : ∀ s : {s : ℂ // 1 < s.re}, finiteHeckeL ψ s = finiteHeckeL η s) (z : ℂ)
    (hz : 0 < D(ψ,z) ∨ 0 < D(η,z)) : D(ψ,z) = D(η,z) := by
  have hpos : 0 < z.re := hz.elim (positive_divisor_re_pos ψ z) (positive_divisor_re_pos η z)
  let A (χ : U) (w : ℂ) := (heckeGammaFactor χ w)⁻¹ * continuedCompletedHeckeL χ w
  have hm (χ : U) : MeromorphicOn (A χ) univ := fun w hw ↦
    ((differentiable_inv_heckeGammaFactor χ).analyticAt w).meromorphicAt.mul
      ((continuedCompletedHeckeL_spec χ).1 hw).meromorphicAt
  have hA (χ : U) (s : {s : ℂ // 1 < s.re}) : A χ s.val = finiteHeckeL χ s := by
    dsimp only [A]
    rw [(continuedCompletedHeckeL_spec χ).2 s]
    exact inv_mul_cancel_left₀ (heckeGammaFactor_ne_zero_of_re_pos χ (zero_lt_one.trans s.property)) _
  have htop : meromorphicOrderAt (A ψ - A η) (2 : ℂ) = ⊤ := by
    apply meromorphicOrderAt_eq_top_iff.mpr
    have hr : ∀ᶠ w : ℂ in 𝓝 (2 : ℂ), 1 < w.re :=
      (isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by norm_num)
    filter_upwards [hr.filter_mono nhdsWithin_le_nhds] with w hw
    exact sub_eq_zero.mpr ((hA ψ ⟨w,hw⟩).trans ((heq ⟨w,hw⟩).trans (hA η ⟨w,hw⟩).symm))
  have ht := ((hm ψ).sub (hm η)).meromorphicOrderAt_eq_top_of_isPreconnected
    isPreconnected_univ (mem_univ (2 : ℂ)) (mem_univ z) htop
  have hgerm : A ψ =ᶠ[𝓝[≠] z] A η :=
    (meromorphicOrderAt_eq_top_iff.mp ht).mono fun _ hw ↦ sub_eq_zero.mp hw
  have ho (χ : U) : meromorphicOrderAt (A χ) z = meromorphicOrderAt (continuedCompletedHeckeL χ) z :=
    meromorphicOrderAt_mul_of_ne_zero ((differentiable_inv_heckeGammaFactor χ).analyticAt z)
      (inv_ne_zero (heckeGammaFactor_ne_zero_of_re_pos χ hpos))
  rw [MeromorphicOn.divisor_apply (continuedCompletedHeckeL_spec ψ).1.meromorphicOn (mem_univ _),
    MeromorphicOn.divisor_apply (continuedCompletedHeckeL_spec η).1.meromorphicOn (mem_univ _),
    ← ho ψ, ← ho η, meromorphicOrderAt_congr hgerm]

/-- The zeta factorizations of two relative quadratic fields and arithmetic equivalence
of the top fields suffice for equality of the two ordinary Hecke series. For the elliptic
3-torsion construction, see de Smit, *Generating arithmetically equivalent number fields
with elliptic curves*, §3, pp. 395–396. -/
theorem finiteHeckeL_eq_of_relative_zeta (ψ η : U) (E₁ E₂ : Type*) [Field E₁] [Field E₂]
    [NumberField E₁] [NumberField E₂]
    (h₁ : ∀ s : {s : ℂ // 1 < s.re}, dedekindZeta E₁ s = dedekindZeta F s * finiteHeckeL ψ s)
    (h₂ : ∀ s : {s : ℂ // 1 < s.re}, dedekindZeta E₂ s = dedekindZeta F s * finiteHeckeL η s)
    (he : ∀ s : {s : ℂ // 1 < s.re}, dedekindZeta E₁ s = dedekindZeta E₂ s)
    (s : {s : ℂ // 1 < s.re}) : finiteHeckeL ψ s = finiteHeckeL η s := by
  have hζ := completedHeckeL_one_eq_dedekindZeta (F := F) s
  rw [← heckeGammaFactor_one] at hζ
  have hbase : finiteHeckeL (1 : U) s = dedekindZeta F s :=
    mul_left_cancel₀ (heckeGammaFactor_ne_zero_of_re_pos (1 : U) (zero_lt_one.trans s.property)) hζ
  apply mul_left_cancel₀ (hbase ▸ finiteHeckeL_ne_zero_of_one_lt_re (1 : U) s)
  exact (h₁ s).symm.trans ((he s).trans (h₂ s))

/-- Paper: Theorem 12.5.1.1, pp. 519–520. Two distinct quadratic Hecke characters with
equal ordinary or completed functions give a real inversion-even physical test. Its only
normalized Mellin samples are opposite and nonzero throughout the off-axis open strip.
The full exterior sum vanishes, with both edges, for every norm section and width. -/
theorem exists_quadraticPair_exteriorZeros (ψ η : U) (hψ : ψ ^ 2 = 1) (hη : η ^ 2 = 1)
    (hne : ψ ≠ η) (hL : (∀ s : {s : ℂ // 1 < s.re}, finiteHeckeL ψ s = finiteHeckeL η s) ∨
      continuedCompletedHeckeL ψ = continuedCompletedHeckeL η) :
    ∃ (g : ℝ → ℂ) (φ : BruhatCompactSupport G),
      ContDiff ℝ ∞ g ∧ HasCompactSupport g ∧ Function.Even g ∧ g 0 = 0 ∧
      (∀ x, φ.val x = ((ψ x : ℂ) - (η x : ℂ)) * g (logIdeleClassNorm F x) / V) ∧
      (∀ x, conj (φ.val x) = φ.val x) ∧ (∀ x, φ.val x⁻¹ = φ.val x) ∧
      (∀ u : (N).ker, φ.val u.val = 0) ∧ (∃ x, φ.val x ≠ 0) ∧
      (∀ w : ℂ, M(φ,ψ,w) = bilateralLaplace g w ∧ M(φ,η,w) = -bilateralLaplace g w) ∧
      (∀ w : ℂ, 0 < |w.re| → |w.re| < 1 / 2 → bilateralLaplace g w ≠ 0) ∧
      ∀ (τ : ℝ≥0ˣ →ₜ* G), RightInverse τ N →
        (∀ χ : Chars(τ), χ.val ≠ ψ → χ.val ≠ η → ∀ w, M(φ,χ.val,w) = 0) ∧
        ∀ α : ℝ, HasSum (fun z : Sites(τ,α) ↦ (D(z.val.1.val,z.val.2) : ℂ) *
          M(φ,z.val.1.val,z.val.2 - 1 / 2)) 0 := by
  obtain ⟨g, hg, hc, he, hr, hz, hd, _⟩ := exists_evenRadialDetector
  obtain ⟨p, hp⟩ := exists_characterNormTest (F := F) ψ g hg hc
  obtain ⟨q, hq⟩ := exists_characterNormTest (F := F) η g hg hc
  let φ : BruhatCompactSupport G := V⁻¹ • (p - q)
  have hφ (x : G) : φ.val x = ((ψ x : ℂ) - (η x : ℂ)) * g (logIdeleClassNorm F x) / V := by
    change V⁻¹ * (p.val x - q.val x) = _
    rw [hp, hq]
    ring
  have hpair (x : G) : φ.val x = ((ψ⁻¹ x : ℂ) - (η⁻¹ x : ℂ)) *
      g (logIdeleClassNorm F x) / V := by
    rw [quadratic_inv ψ hψ, quadratic_inv η hη, hφ]
  have hrows (τ : ℝ≥0ˣ →ₜ* G) (hτ : RightInverse τ N) (χ : Chars(τ)) (w : ℂ) :
      M(φ,χ.val,w) = (if χ.val = ψ then bilateralLaplace g w else 0) -
        (if χ.val = η then bilateralLaplace g w else 0) := by
    let P : Chars(τ) := ⟨ψ, quadratic_on_section ψ hψ τ⟩
    let Q : Chars(τ) := ⟨η, quadratic_on_section η hη τ⟩
    simpa only [Subtype.ext_iff, P, Q, bilateralLaplace] using
      mellin_normalizedPair τ hτ P Q χ g hg hc φ hpair w
  let σ : ℝ≥0ˣ →ₜ* G := ⟨(QuotientGroup.mk' _).comp (canonicalIdeleNormSection F),
    continuous_quotient_mk'.comp (canonicalIdeleNormSection_continuous _)⟩
  have hσ : RightInverse σ N := canonicalIdeleNormSection_rightInverse F
  have hsamp (w : ℂ) : M(φ,ψ,w) = bilateralLaplace g w ∧ M(φ,η,w) = -bilateralLaplace g w := by
    have a := hrows σ hσ ⟨ψ, quadratic_on_section ψ hψ σ⟩ w
    have b := hrows σ hσ ⟨η, quadratic_on_section η hη σ⟩ w
    simpa only [ite_eq_left rfl, ite_true, ite_eq_right hne, ite_eq_right (Ne.symm hne), sub_zero, zero_sub]
      using And.intro a b
  refine ⟨g, φ, hg, hc, he, hz, hφ, fun x ↦ ?_, fun x ↦ ?_, fun u ↦ ?_, ?_, hsamp, hd,
    fun τ hτ ↦ ⟨fun χ h₁ h₂ w ↦ ?_, fun α ↦ ?_⟩⟩
  · rw [hφ, map_div₀, map_mul, map_sub, quadratic_values_real ψ hψ,
      quadratic_values_real η hη, hr, Complex.conj_ofReal]
  · have hinv (χ : U) (hχ : χ ^ 2 = 1) : χ x⁻¹ = χ x :=
      (map_inv χ x).trans (congrArg (fun θ : U ↦ θ x) (quadratic_inv χ hχ))
    have hl : logIdeleClassNorm F x⁻¹ = -logIdeleClassNorm F x := by
      change Real.log _ = -Real.log _
      simp [map_inv]
    rw [hφ, hφ, hinv ψ hψ, hinv η hη, hl, he]
  · rw [hφ]
    have hl : logIdeleClassNorm F u.val = 0 := by
      change Real.log ((N u.val).val : ℝ) = 0
      rw [u.property]
      simp
    rw [hl, hz, mul_zero, zero_div]
  · by_contra! hzero
    have h := (hsamp (1 / 4)).1
    simp [modulatedFourierMellin, hzero] at h
    exact hd (1 / 4) (by norm_num) (by norm_num) (by simpa only [one_div] using h.symm)
  · rw [hrows τ hτ, ite_eq_right h₁, ite_eq_right h₂, sub_self]
  · let P : Chars(τ) := ⟨ψ, quadratic_on_section ψ hψ τ⟩
    let Q : Chars(τ) := ⟨η, quadratic_on_section η hη τ⟩
    let f (x : ℝ) := g x / V
    have hfc : HasCompactSupport f := HasCompactSupport.intro hc.isCompact fun x hx ↦ by
      change g x / V = 0
      rw [image_eq_zero_of_notMem_tsupport hx, zero_div]
    apply hasSum_exteriorZeros_characterPair τ hτ P Q f (hg.div_const _) hfc α
    · intro z _ hz
      rcases hL with hfinite | hcompleted
      · exact positive_completed_divisors_eq_of_finiteHeckeL_eq ψ η hfinite z hz
      · exact congrArg (fun L : ℂ → ℂ ↦ MeromorphicOn.divisor L univ z) hcompleted
    · intro x
      change φ.val x = ((ψ⁻¹ x : ℂ) - (η⁻¹ x : ℂ)) * (g _ / V)
      rw [hpair]
      ring

end

end RiemannMasullo.Isolated.AngularPair
