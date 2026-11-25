module

import Mathlib.Geometry.Manifold.PartitionOfUnity
public import RiemannMasullo.Ch12_TraceGeometric.Sec5
public import RiemannMasullo.AppB_AnalyticNT.PolynomialIdealSamples
public import RiemannMasullo.ForMathlib.Analysis.Analytic.ZeroLatticeEventuallyCertified
public import RiemannMasullo.ForMathlib.Analysis.Analytic.ZeroDensity
public import RiemannMasullo.ForMathlib.Analysis.Analytic.ZeroLatticeSchwartz
public import RiemannMasullo.ForMathlib.Analysis.Fourier.SchwartzLaplaceAxis
public import RiemannMasullo.ForMathlib.MeasureTheory.Integral.PolynomialWindow
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
import RiemannMasullo.AppB_AnalyticNT.Sec4b
import RiemannMasullo.ForMathlib.Analysis.Analytic.CauchyWindow

public import RiemannMasullo.Ch01_Introduction.Sec4_PoissonCertificate
public import RiemannMasullo.Ch01_Introduction.Sec4_HeckeGreenExterior
public import RiemannMasullo.AppB_AnalyticNT.Sec4b_BoundaryHeckeGreen
public import RiemannMasullo.AppB_AnalyticNT.HeckeFiniteLogGreen

/-! # Isolated statements of §12.5

Statements of the section that are neither proved nor refuted and that nothing else in Lean
uses, with what follows from them (`AGENTS.md`, "False statements and gaps"). Nothing imports
this file.

## The projective strip kernel needed for (12.5.1.4)

The first theorem supplies the kernel hypothesis of the smoothened diagonal formula in §12.5.
The second theorem specializes that formula to this kernel.

Later sections recover the critical-line divisor mass with its full multiplicity from the finite
Hecke continuation. They use a shrinking regularized density and a finite lattice of consecutive
absolute values. A positive full-site sum then gives a lower-comparison criterion for the
exterior sum in Theorem 12.5.1.1, pp. 519–520.
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
Gap: The projective norm estimate for the geometric component of the output is missing.
Nothing in the Lean uses this statement, and it is not known how it connects with the rest of
the proof in Lean; in the paper it is used on pp. 520, 522. -/
theorem exists_projectiveKernel_stripTestAction_spectralProjection
    (φ : BruhatCompactSupport C𝔽) (_hφ : ∀ g : C₁, φ.val g = 0)
    {α s : ℝ} (hα : 0 < α) (hs : 3 ≤ s) :
    ∃ K, sobolevProjectiveKernelOperator (F := F) hα.le hs₀(hs) K =
      (hardySobolevTestAction μ𝔽 m𝔽 (-α) α s ((neg_nonpos.mpr hα.le).trans hα.le) hs₀(hs) φ).comp
        (spectralProjection (F := F) (1 / 2) hα.le hs₀(hs)) := by
  sorry

/-- Paper: (12.5.1.4), p. 520. The smoothened geometric diagonal is Haar-integrable, and the
strip zero terms sum absolutely to its negative integral.
Deviation: As in §12.5 of the library, a measurable D′-sequence specifies the smoothening,
and the sum uses the closed strip with strict reciprocal-weight multiplicities on its edges.
It agrees with the printed interior sum when both edges are zero-free.
It is proved from the kernel existence statement above, which is open, so it is no more
established than that statement. Nothing in the Lean uses it. -/
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

/-! ## Integer ordinates and translated Poisson mass

The unit cells cover the full ordinate line. A single off-line site and its
same-character reflection cost strictly more than six fifths in one of them.
-/

namespace PoissonCertificate

open RiemannMasullo.HeckePoisson

local notation "U𝔽" => PontryaginDual C𝔽
local notation "ord(" χ ", " z ")" =>
  MeromorphicOn.divisor (continuedCompletedHeckeL (F := F) χ) univ z

local notation "ext(" σ ", " a ")" =>
  {p : {η : U𝔽 // ∀ u : ℝ≥0ˣ, η (σ u) = 1} × ℂ //
    0 < ord(p.1.val, p.2) ∧ (a : ℝ) ≤ |p.2.re - 1 / 2|}

/-- Paper: Theorem 12.5.1.1, pp. 519–520. The omitted-zero cancellation at one half-width. -/
def exteriorCancellation (σ : ℝ≥0ˣ →ₜ* C𝔽) (a : ℝ) : Prop :=
  ∀ φ : BruhatCompactSupport C𝔽, (∀ g : (ideleClassNorm F).ker, φ.val g = 0) →
    HasSum (fun z : ext(σ, a) ↦ (ord(z.val.1.val, z.val.2) : ℂ) *
      ∫ g, φ.val g * ideleClassNormTwist z.val.1.val (z.val.2 - 1 / 2) g
        ∂ideleClassTamagawaMeasure F) 0

private theorem exteriorCancellation_iff_empty (σ : ℝ≥0ˣ →ₜ* C𝔽)
    (hσ : Function.RightInverse σ (ideleClassNorm F)) (a : ℝ) :
    exteriorCancellation σ a ↔ IsEmpty ext(σ, a) := by
  simpa only [exteriorCancellation, modulatedFourierMellin, relativeVerticalStrip,
    Set.preimage_univ, Set.indicator_univ] using hasSum_exteriorZeros_iff_isEmpty σ hσ a

/-- Paper: Theorem 12.5.1.1, pp. 519–520. The all-width omitted-zero cancellation is equivalent
to one numerical threshold at the integer ordinates for each normalized
character. Both sides use the actual divisor of the same completed function. -/
theorem all_widths_iff_integer_mass (σ : ℝ≥0ˣ →ₜ* C𝔽)
    (hσ : Function.RightInverse σ (ideleClassNorm F)) :
    (∀ a > 0, exteriorCancellation σ a) ↔
      ∀ χ : U𝔽, (∀ u : ℝ≥0ˣ, χ (σ u) = 1) →
        ∀ k : ℤ, fullMass χ k - centralMass χ k ≤ 6 / 5 := by
  constructor
  · intro h χ hχ
    apply (criticalLine_iff_integer_mass χ).mp
    intro z
    by_contra hz
    have he := (exteriorCancellation_iff_empty σ hσ _).mp
      (h |z.val.re - 1 / 2| (abs_pos.mpr (sub_ne_zero.mpr hz)))
    exact he.false ⟨(⟨χ, hχ⟩, z.val), z.property, le_rfl⟩
  · intro h a ha
    apply (exteriorCancellation_iff_empty σ hσ a).mpr
    refine ⟨fun z ↦ ?_⟩
    have he := (criticalLine_iff_integer_mass z.val.1.val).mpr
      (h z.val.1.val z.val.1.property) ⟨z.val.2, z.property.1⟩
    change z.val.2.re = 1 / 2 at he
    have := z.property.2
    rw [he, sub_self, abs_zero] at this
    exact (not_le_of_gt ha) this

/-- Paper: Theorem 12.5.1.1, pp. 519–520. With the translated explicit formula supplied, the all-width
criterion compares the pole-cleared arithmetic logarithmic derivative with
the complete central-line contribution at integer centers. -/
theorem all_widths_iff_integer_logDerivative (σ : ℝ≥0ˣ →ₜ* C𝔽)
    (hσ : Function.RightInverse σ (ideleClassNorm F))
    (hformula : ∀ χ : U𝔽, (∀ u : ℝ≥0ˣ, χ (σ u) = 1) →
      ∀ k : ℤ, HasSum (siteWeight (χ := χ) k) (normalizedLogDerivative χ k)) :
    (∀ a > 0, exteriorCancellation σ a) ↔
      ∀ χ : U𝔽, (∀ u : ℝ≥0ˣ, χ (σ u) = 1) →
        ∀ k : ℤ, normalizedLogDerivative χ k - centralMass χ k ≤ 6 / 5 := by
  rw [all_widths_iff_integer_mass σ hσ]
  constructor <;> intro h χ hχ k <;>
    simpa only [fullMass, (hformula χ hχ k).tsum_eq] using h χ hχ k

end PoissonCertificate

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

namespace criticalFiniteHeckeL

/- When the two sections are compiled separately, Lean gives different names to their
proofs of the same instance propositions. Preserve the critical-line definitions' original
kernel expressions by selecting these names only in their four right-hand sides. -/
set_option linter.auxLemma false

/-- The normality proof used in the original critical-line definitions. -/
@[scoped instance] theorem _proof_1 :
    (NumberField.IdeleGroup.principalSubgroup (NumberField.RingOfIntegers F) F).Normal :=
  Subgroup.normal_of_isMulCommutative _

/-- The lower bound on the numeral two used in the original critical-line definitions. -/
@[scoped instance] theorem _proof_2 : (1 + 1).AtLeastTwo := Nat.instAtLeastTwoHAddOfNat 1

end criticalFiniteHeckeL

section CriticalFiniteHeckeDensity

open Complex Filter Function Topology

local notation "cl(" t ")" => ((1 / 2 : ℂ) + ((t : ℝ) : ℂ) * I)
local notation "completed(" χ ")" => (continuedCompletedHeckeL (F := F) χ)
local notation "ord(" χ ", " z ")" => MeromorphicOn.divisor completed(χ) univ z

private theorem criticalLine_re (t : ℝ) : cl(t).re = 1 / 2 := by norm_num [Complex.mul_re]
private theorem criticalLine_im (t : ℝ) : cl(t).im = t := by norm_num [Complex.mul_im]
private theorem criticalLine_rebuild (z : ℂ) (hz : z.re = 1 / 2) : cl(z.im) = z :=
  Complex.ext ((criticalLine_re _).trans hz.symm) (criticalLine_im _)

private theorem analyticAt_criticalLine (t : ℝ) : AnalyticAt ℝ (fun x : ℝ ↦ cl(x)) t :=
  analyticAt_const.add ((Complex.ofRealCLM.analyticAt t).mul analyticAt_const)

/-- Restricting a holomorphic germ to the parametrized vertical line preserves its order.
The complex unit in the real factorization is multiplied by `I ^ n`. -/
private theorem analyticOrderAt_criticalLine {A : ℂ → ℂ} {t : ℝ} (hA : AnalyticAt ℂ A cl(t)) :
    AnalyticAt ℝ (fun x : ℝ ↦ A cl(x)) t ∧
    analyticOrderAt (fun x : ℝ ↦ A cl(x)) t = analyticOrderAt A cl(t) := by
  have hline := analyticAt_criticalLine t
  have hres : AnalyticAt ℝ (fun x : ℝ ↦ A cl(x)) t :=
    (hA.restrictScalars (𝕜 := ℝ)).comp (f := fun x : ℝ ↦ cl(x)) hline
  refine ⟨hres, ?_⟩
  by_cases htop : analyticOrderAt A cl(t) = ⊤
  · rw [htop, analyticOrderAt_eq_top]
    exact hline.continuousAt.tendsto.eventually (analyticOrderAt_eq_top.mp htop)
  let n := analyticOrderNatAt A cl(t)
  have hn : analyticOrderAt A cl(t) = (n : ℕ∞) := (Nat.cast_analyticOrderNatAt htop).symm
  obtain ⟨u, hu, hu0, hfac⟩ := hA.analyticOrderAt_eq_natCast.mp hn
  rw [hn, hres.analyticOrderAt_eq_natCast]
  refine ⟨fun x : ℝ ↦ I ^ n * u cl(x),
    analyticAt_const.mul ((hu.restrictScalars (𝕜 := ℝ)).comp (f := fun x : ℝ ↦ cl(x)) hline),
    mul_ne_zero (pow_ne_zero _ I_ne_zero) hu0, ?_⟩
  filter_upwards [hline.continuousAt.tendsto.eventually hfac] with x hx
  have he : cl(x) - cl(t) = ((x - t : ℝ) : ℂ) * I := by push_cast; ring
  rw [hx, he, smul_eq_mul, Complex.real_smul, Complex.ofReal_pow, mul_pow, mul_assoc]

private theorem analyticAt_completedHecke_of_openStrip (χ : PontryaginDual C𝔽) {z : ℂ}
    (ha : 0 < z.re) (hb : z.re < 1) : AnalyticAt ℂ completed(χ) z := by
  obtain ⟨hm, he⟩ := continuedCompletedHeckeL_spec χ
  by_cases hχ : χ.toMonoidHom.comp (ideleClassNorm F).ker.subtype = 1
  · obtain ⟨r, ⟨-, -, -, hhol⟩, -⟩ := completedHeckeL_continuation_simplePoles χ _ hm he hχ
    apply hhol z
    simp only [mem_compl_iff, mem_insert_iff, mem_singleton_iff]
    rintro (h | h)
    · have hr := congrArg Complex.re h
      simp [Complex.mul_re] at hr
      linarith
    · have hr := congrArg Complex.re h
      simp [Complex.mul_re] at hr
      linarith
  · exact (completedHeckeL_continuation_entire χ _ hm he hχ).analyticAt z

private theorem completedHecke_order_ne_top (χ : PontryaginDual C𝔽) (z : ℂ) :
    meromorphicOrderAt completed(χ) z ≠ ⊤ := by
  obtain ⟨hm, he⟩ := continuedCompletedHeckeL_spec χ
  have h₂ : (1 : ℝ) < (2 : ℂ).re := by norm_num
  have hval : completed(χ) 2 ≠ 0 := by
    rw [he ⟨2, h₂⟩]
    exact mul_ne_zero (heckeGammaFactor_ne_zero_of_re_pos χ (zero_lt_one.trans h₂))
      (finiteHeckeL_ne_zero_of_one_lt_re χ ⟨2, h₂⟩)
  apply hm.meromorphicOn.meromorphicOrderAt_ne_top_of_isPreconnected
    isPreconnected_univ (mem_univ (2 : ℂ)) (mem_univ z)
  rw [(hm (mem_univ _)).meromorphicOrderAt_eq_zero_iff.mpr hval]
  exact WithTop.coe_ne_top

/-- The finite Hecke function on the critical line, formed by removing the archimedean
gamma factor from the specified meromorphic continuation of the completed function. -/
def criticalFiniteHeckeL : PontryaginDual C𝔽 → ℝ → ℂ :=
  open scoped RiemannMasullo.Isolated.criticalFiniteHeckeL in
  fun (χ : PontryaginDual C𝔽) (t : ℝ) ↦ completed(χ) cl(t) * (heckeGammaFactor χ cl(t))⁻¹

/-- Every normal-form continuation of the finite Euler product agrees with
`criticalFiniteHeckeL` at every point of the critical line. -/
theorem criticalFiniteHeckeL_eq_continuation (χ : PontryaginDual C𝔽) (L : ℂ → ℂ)
    (hL : MeromorphicNFOn L univ)
    (he : ∀ z : {z : ℂ // 1 < z.re}, L z = finiteHeckeL χ z) :
    criticalFiniteHeckeL χ = fun t : ℝ ↦ L cl(t) := by
  let M (z : ℂ) := completed(χ) z * (heckeGammaFactor χ z)⁻¹
  obtain ⟨hΛ, hΛe⟩ := continuedCompletedHeckeL_spec χ
  have hM : MeromorphicOn M univ := fun z hz ↦ (hΛ hz).meromorphicAt.mul
    ((differentiable_inv_heckeGammaFactor χ).analyticAt z).meromorphicAt
  have hEq := heckeEulerProductOutside_eq_finite_nf_eq L M hL.meromorphicOn hM (fun z hz ↦ by
    rw [he ⟨z, hz⟩]
    dsimp only [M]
    rw [hΛe ⟨z, hz⟩]
    change finiteHeckeL χ ⟨z, hz⟩ = heckeGammaFactor χ z * finiteHeckeL χ ⟨z, hz⟩ * _
    rw [mul_right_comm, mul_inv_cancel₀ (heckeGammaFactor_ne_zero_of_re_pos χ (zero_lt_one.trans hz)),
      one_mul])
  rw [toMeromorphicNFOn_eq_self.mpr hL] at hEq
  funext t
  have hpos : 0 < cl(t).re := by rw [criticalLine_re]; norm_num
  have hlt : cl(t).re < 1 := by rw [criticalLine_re]; norm_num
  have hreg : AnalyticAt ℂ M cl(t) := (analyticAt_completedHecke_of_openStrip χ hpos hlt).mul
    ((differentiable_inv_heckeGammaFactor χ).analyticAt _)
  rw [hEq, toMeromorphicNFOn_eq_toMeromorphicNFAt hM (mem_univ _),
    toMeromorphicNFAt_eq_self.mpr hreg.meromorphicNFAt]
  rfl

/-- The finite critical-line function is real analytic with a nonzero germ. Its real
analytic order, including at multiple zeros, equals the integer divisor of the completed
Hecke function at the corresponding complex point. -/
theorem criticalFiniteHeckeL_order (χ : PontryaginDual C𝔽) (t : ℝ) :
    AnalyticAt ℝ (criticalFiniteHeckeL χ) t ∧
    ¬ (∀ᶠ u in 𝓝 t, criticalFiniteHeckeL χ u = 0) ∧
    (analyticOrderNatAt (criticalFiniteHeckeL χ) t : ℤ) = ord(χ, cl(t)) := by
  let M := completed(χ) * (fun z ↦ (heckeGammaFactor χ z)⁻¹)
  have hpos : 0 < cl(t).re := by rw [criticalLine_re]; norm_num
  have hlt : cl(t).re < 1 := by rw [criticalLine_re]; norm_num
  have hΛ := analyticAt_completedHecke_of_openStrip χ hpos hlt
  have hΓ := (differentiable_inv_heckeGammaFactor χ).analyticAt cl(t)
  have hunit : (heckeGammaFactor χ cl(t))⁻¹ ≠ 0 :=
    inv_ne_zero (heckeGammaFactor_ne_zero_of_re_pos χ hpos)
  have hM : AnalyticAt ℂ M cl(t) := hΛ.mul hΓ
  obtain ⟨hreal, hv⟩ := analyticOrderAt_criticalLine hM
  have hA : analyticOrderAt (criticalFiniteHeckeL χ) t = analyticOrderAt completed(χ) cl(t) := by
    change analyticOrderAt (fun u : ℝ ↦ M cl(u)) t = _
    rw [hv, show analyticOrderAt M cl(t) = _ + _ from analyticOrderAt_mul hΛ hΓ,
      hΓ.analyticOrderAt_eq_zero.mpr hunit, add_zero]
  have hfinite : analyticOrderAt (criticalFiniteHeckeL χ) t ≠ ⊤ := by
    intro ht
    apply completedHecke_order_ne_top χ cl(t)
    rw [hΛ.meromorphicOrderAt_eq, ← hA, ht, ENat.map_top]
  refine ⟨hreal, fun h ↦ hfinite (analyticOrderAt_eq_top.mpr h), ?_⟩
  rw [MeromorphicOn.divisor_apply (continuedCompletedHeckeL_spec χ).1.meromorphicOn (mem_univ _),
    hΛ.meromorphicOrderAt_eq, ← hA, ← Nat.cast_analyticOrderNatAt hfinite, ENat.map_natCast,
    WithTop.untop₀_coe]

private theorem critical_zero_moments_eq (χ : PontryaginDual C𝔽) (g : ℝ → ℝ) :
    (∑' t : {t : ℝ // criticalFiniteHeckeL χ t = 0},
      (analyticOrderNatAt (criticalFiniteHeckeL χ) t.val : ℝ) * g t.val) =
      ∑' z : {z : ℂ // 0 < ord(χ,z) ∧ z.re = 1/2}, ((ord(χ,z.val)).toNat : ℝ) * g z.val.im := by
  classical
  let f := criticalFiniteHeckeL χ
  let Z := {t : ℝ // f t = 0}
  let C := {z : ℂ // 0 < ord(χ, z) ∧ z.re = 1 / 2}
  have hlocal (t : ℝ) := criticalFiniteHeckeL_order χ t
  have hfin (t : ℝ) : analyticOrderAt f t ≠ ⊤ := fun ht ↦ (hlocal t).2.1 (analyticOrderAt_eq_top.mp ht)
  have hpos (t : ℝ) : f t = 0 ↔ 0 < ord(χ, cl(t)) := by
    rw [← (hlocal t).2.2]
    rw [← (hlocal t).1.analyticOrderAt_ne_zero, ← Nat.cast_analyticOrderNatAt (hfin t)]
    simp [f, Nat.pos_iff_ne_zero]
  let e : Z ≃ C :=
    { toFun := fun t ↦ ⟨cl(t.val), (hpos t).mp t.2, criticalLine_re _⟩
      invFun := fun z ↦ ⟨z.val.im, (hpos _).mpr (by rw [criticalLine_rebuild _ z.2.2]; exact z.2.1)⟩
      left_inv := fun t ↦ Subtype.ext (criticalLine_im _)
      right_inv := fun z ↦ Subtype.ext (criticalLine_rebuild _ z.2.2) }
  have hsum : (∑' t : Z, (analyticOrderNatAt f t.val : ℝ) * g t.val) =
      ∑' z : C, ((ord(χ, z.val)).toNat : ℝ) * g z.val.im := by
    calc
      _ = ∑' t : Z, ((ord(χ, (e t).val)).toNat : ℝ) * g (e t).val.im := by
        apply tsum_congr
        intro t
        change _ = ((ord(χ, cl(t.val))).toNat : ℝ) * g cl(t.val).im
        rw [criticalLine_im, ← (hlocal t).2.2, Int.toNat_natCast]
      _ = _ := e.tsum_eq (fun z : C ↦ ((ord(χ, z.val)).toNat : ℝ) * g z.val.im)
  exact hsum

/-- Integrating the finite Hecke function's regularized logarithmic-derivative density
against a signed compact continuous test recovers the completed divisor on exactly its
occupied central sites, with full multiplicities. -/
theorem tendsto_integral_criticalFiniteHeckeL (χ : PontryaginDual C𝔽) {g : ℝ → ℝ}
    (hg : Continuous g) (hgc : HasCompactSupport g) :
    Tendsto (fun η : ℝ ↦ ∫ t, g t * analyticZeroDensity (criticalFiniteHeckeL χ) η t) (𝓝[>] 0)
      (𝓝 (∑' z : {z : ℂ // 0 < ord(χ, z) ∧ z.re = 1 / 2},
        ((ord(χ, z.val)).toNat : ℝ) * g z.val.im)) := by
  classical
  let f := criticalFiniteHeckeL χ
  let C := {z : ℂ // 0 < ord(χ,z) ∧ z.re = 1/2}
  have hlocal (t : ℝ) := criticalFiniteHeckeL_order χ t
  have hfin (t : ℝ) : analyticOrderAt f t ≠ ⊤ := fun ht ↦ (hlocal t).2.1 (analyticOrderAt_eq_top.mp ht)
  have hlim := tendsto_integral_analyticZeroDensity (f := f) hg hgc
    (fun t _ ↦ (hlocal t).1) (fun t _ ↦ hfin t)
  have hsum := critical_zero_moments_eq χ g
  change Tendsto (fun η : ℝ ↦ ∫ t, g t * analyticZeroDensity f η t) (𝓝[>] 0)
    (𝓝 (∑' z : C, ((ord(χ, z.val)).toNat : ℝ) * g z.val.im))
  rw [← hsum]
  exact hlim

end CriticalFiniteHeckeDensity

section CriticalSchwartzDensity

open Complex Filter Function Topology
open scoped _root_.SchwartzMap ContDiff ENNReal FourierTransform NNReal

local notation "cl(" t ")" => ((1 / 2 : ℂ) + ((t : ℝ) : ℂ) * I)
local notation "ord(" χ ", " z ")" => MeromorphicOn.divisor (continuedCompletedHeckeL (F := F) χ) univ z
local notation "central(" χ ")" => {z : ℂ // 0 < ord(χ, z) ∧ z.re = 1 / 2}
local notation "mult(" χ ", " z ")" => (ord(χ, (z : ℂ))).toNat
local notation "density(" χ ", " η ")" => analyticZeroDensity (criticalFiniteHeckeL χ) η

/-- The positive atomic measure on the ordinates of the central zeros of the completed
Hecke function. Each point has mass equal to its full analytic multiplicity. -/
def criticalHeckeZeroMeasure : PontryaginDual C𝔽 → Measure ℝ :=
  open scoped RiemannMasullo.Isolated.criticalFiniteHeckeL in
  fun (χ : PontryaginDual C𝔽) ↦ Measure.sum fun z : central(χ) ↦ (mult(χ, z) : ℝ≥0∞) • Measure.dirac z.val.im

private theorem criticalHeckeZeroMeasure_finite_sites (χ : PontryaginDual C𝔽)
    {K : Set ℝ} (hK : IsCompact K) : {z : central(χ) | z.val.im ∈ K}.Finite := by
  let D := MeromorphicOn.divisor (continuedCompletedHeckeL (F := F) χ) univ
  have hloc : LocallyFiniteSupport (fun z ↦ D z) :=
    fun z ↦ D.supportLocallyFiniteWithinDomain z (mem_univ z)
  have hline : Continuous (fun t : ℝ ↦ cl(t)) := by fun_prop
  have hf := hloc.finite_inter_support_of_isCompact (hK.image hline)
  refine (hf.preimage (f := fun z : central(χ) ↦ z.val) Subtype.val_injective.injOn).subset ?_
  intro z hz
  exact ⟨⟨z.val.im, hz, criticalLine_rebuild _ z.property.2⟩, z.property.1.ne'⟩

/-- Local finiteness of the completed divisor makes the central atomic measure finite on
every compact set of ordinates. -/
instance criticalHeckeZeroMeasure_finiteOnCompacts (χ : PontryaginDual C𝔽) :
    IsFiniteMeasureOnCompacts (criticalHeckeZeroMeasure χ) where
  lt_top_of_isCompact {K} hK := by
    classical
    let hfin := criticalHeckeZeroMeasure_finite_sites χ hK
    have hv (z : central(χ)) : ((mult(χ, z) : ℝ≥0∞) • Measure.dirac z.val.im : Measure ℝ) K =
        if z.val.im ∈ K then (mult(χ, z) : ℝ≥0∞) else 0 := by
      by_cases h : z.val.im ∈ K <;> simp [Measure.dirac_apply' _ hK.measurableSet, h]
    rw [criticalHeckeZeroMeasure, Measure.sum_apply _ hK.measurableSet, tsum_congr hv]
    rw [tsum_eq_sum (s := hfin.toFinset) (f := fun z : central(χ) ↦
      if z.val.im ∈ K then (mult(χ, z) : ℝ≥0∞) else 0) (fun z hz ↦ by
        simp [show z.val.im ∉ K from fun hm ↦ hz (hfin.mem_toFinset.mpr hm)])]
    apply ENNReal.sum_lt_top.mpr
    intro z _
    split <;> finiteness

/-- Integrating against the central zero measure is an unconditionally convergent sum over
the exact complex central-site subtype, with full multiplicities and ordinate evaluation. -/
theorem hasSum_criticalHeckeZeroMeasure (χ : PontryaginDual C𝔽) {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] (g : ℝ → E)
    (hg : Integrable g (criticalHeckeZeroMeasure χ)) :
    HasSum (fun z : central(χ) ↦ (mult(χ, z) : ℝ) • g z.val.im)
      (∫ t, g t ∂criticalHeckeZeroMeasure χ) := by
  unfold criticalHeckeZeroMeasure at hg ⊢
  simpa only [integral_smul_measure, integral_dirac, ENNReal.toReal_natCast] using
    hasSum_integral_measure hg

/-- The critical finite Hecke density is Borel measurable for every parameter. -/
theorem criticalFiniteHeckeL_density_measurable (χ : PontryaginDual C𝔽) (η : ℝ) :
    Measurable (density(χ, η)) := by
  have hc : Continuous (criticalFiniteHeckeL χ) :=
    continuous_iff_continuousAt.mpr fun t ↦ (criticalFiniteHeckeL_order χ t).1.continuousAt
  have hd : Continuous (deriv (criticalFiniteHeckeL χ)) :=
    continuous_iff_continuousAt.mpr fun t ↦ (criticalFiniteHeckeL_order χ t).1.deriv.continuousAt
  unfold analyticZeroDensity
  fun_prop

private theorem criticalHeckeDensity_norm_le (χ : PontryaginDual C𝔽) {η : ℝ} (hη : 0 < η) (t : ℝ) :
    ‖density(χ, η) t‖ ≤ 1 / (Real.pi * η) := by
  rw [Real.norm_of_nonneg (by unfold analyticZeroDensity; positivity)]
  unfold analyticZeroDensity
  by_cases hd : deriv (criticalFiniteHeckeL χ) t = 0
  · simp only [hd, norm_zero, zero_pow (by decide : 2 ≠ 0), mul_zero, zero_div]
    positivity
  have hs : 0 < η ^ 2 * ‖deriv (criticalFiniteHeckeL χ) t‖ ^ 2 := by positivity
  calc
    _ ≤ (η / Real.pi) * ‖deriv (criticalFiniteHeckeL χ) t‖ ^ 2 /
        (η ^ 2 * ‖deriv (criticalFiniteHeckeL χ) t‖ ^ 2) :=
      div_le_div_of_nonneg_left (by positivity) hs (le_add_of_nonneg_left (sq_nonneg _))
    _ = _ := by field_simp [Real.pi_ne_zero, hη.ne', norm_ne_zero_iff.mpr hd]

private theorem criticalHeckeDensity_integrableOn_compact (χ : PontryaginDual C𝔽)
    {η : ℝ} (hη : 0 < η) {K : Set ℝ} (hK : IsCompact K) : IntegrableOn (density(χ, η)) K := by
  have hc : IntegrableOn (fun _ : ℝ ↦ 1 / (Real.pi * η)) K := integrableOn_const hK.measure_ne_top
  exact hc.mono' (criticalFiniteHeckeL_density_measurable χ η).aestronglyMeasurable
    (ae_of_all _ (criticalHeckeDensity_norm_le χ hη))

/-- At every positive scale the signed Schwartz pairing is an absolutely convergent
Lebesgue integral. -/
theorem integrable_schwartz_mul_criticalFiniteHeckeL_density (χ : PontryaginDual C𝔽)
    {η : ℝ} (hη : 0 < η) (g : 𝓢(ℝ, ℝ)) : Integrable (fun t ↦ g t * density(χ, η) t) := by
  have hmajor : Integrable (fun t ↦ ‖g t‖ * (1 / (Real.pi * η))) := g.integrable.norm.mul_const _
  apply hmajor.mono' (g.continuous.measurable.mul (criticalFiniteHeckeL_density_measurable χ η)).aestronglyMeasurable
  exact ae_of_all _ fun t ↦ by
    change ‖g t * density(χ, η) t‖ ≤ _
    rw [_root_.norm_mul]
    exact mul_le_mul_of_nonneg_left (criticalHeckeDensity_norm_le χ hη t) (norm_nonneg _)

private def criticalHeckeDensityMeasure : PontryaginDual C𝔽 → ℝ → Measure ℝ :=
  open scoped RiemannMasullo.Isolated.criticalFiniteHeckeL in
  fun (χ : PontryaginDual C𝔽) (η : ℝ) ↦ volume.withDensity (fun t ↦ ENNReal.ofReal (density(χ, η) t))

private theorem criticalHeckeDensityMeasure_pairing (χ : PontryaginDual C𝔽)
    {η : ℝ} (hη : 0 < η) {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (g : ℝ → E) :
    (∫ t, g t ∂criticalHeckeDensityMeasure χ η) = ∫ t, density(χ, η) t • g t := by
  unfold criticalHeckeDensityMeasure
  rw [integral_withDensity_eq_integral_toReal_smul₀
    (criticalFiniteHeckeL_density_measurable χ η).aemeasurable.ennreal_ofReal
    (ae_of_all _ fun _ ↦ ENNReal.ofReal_lt_top)]
  exact integral_congr_ae (ae_of_all _ fun t ↦ by
    change (ENNReal.ofReal (density(χ, η) t)).toReal • g t = density(χ, η) t • g t
    rw [ENNReal.toReal_ofReal (by unfold analyticZeroDensity; positivity)])

private theorem criticalHeckeDensityMeasure_compact (χ : PontryaginDual C𝔽) (g : ℝ → ℝ)
    (hg : Continuous g) (hgc : HasCompactSupport g) :
    Tendsto (fun η : ℝ ↦ ∫ t, g t ∂criticalHeckeDensityMeasure χ η) (𝓝[>] 0)
      (𝓝 (∫ t, g t ∂criticalHeckeZeroMeasure χ)) := by
  have hsum := (hasSum_criticalHeckeZeroMeasure χ g (hg.integrable_of_hasCompactSupport hgc)).tsum_eq
  simp only [smul_eq_mul] at hsum
  have h := tendsto_integral_criticalFiniteHeckeL χ hg hgc
  rw [hsum] at h
  apply h.congr'
  filter_upwards [self_mem_nhdsWithin (a := (0 : ℝ)) (s := Ioi 0)] with η hη
  rw [criticalHeckeDensityMeasure_pairing χ hη]
  apply integral_congr_ae
  exact ae_of_all _ fun t ↦ mul_comm _ _

private theorem criticalHeckeDensityMeasure_window (χ : PontryaginDual C𝔽) {η : ℝ} (hη : 0 < η) (k : ℤ) :
    criticalHeckeDensityMeasure χ η (Icc (k : ℝ) (k + 1)) =
      ENNReal.ofReal (∫ t in Icc (k : ℝ) (k + 1), density(χ, η) t) := by
  rw [criticalHeckeDensityMeasure, withDensity_apply _ measurableSet_Icc,
    ← ofReal_integral_eq_lintegral_ofReal (criticalHeckeDensity_integrableOn_compact χ hη isCompact_Icc)]
  exact ae_of_all _ fun t ↦ by unfold analyticZeroDensity; positivity

private theorem integrable_schwartz_of_criticalWindow {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (ν : Measure ℝ) (C : ℝ≥0) (d : ℕ)
    (hν : ∀ k : ℤ, ν (Icc (k : ℝ) (k + 1)) ≤ ENNReal.ofReal ((C : ℝ) * (1 + |(k : ℝ)|) ^ d))
    (g : 𝓢(ℝ, E)) : Integrable g ν := by
  let p : Seminorm ℝ 𝓢(ℝ, E) := (Finset.Iic (d + 2, 0)).sup
    (fun m ↦ _root_.SchwartzMap.seminorm ℝ m.1 m.2)
  have hb (x : ℝ) : (1 + |x|) ^ (d + 2) * ‖g x‖ ≤ 2 ^ (d + 2) * p g := by
    simpa [p, Real.norm_eq_abs] using
      _root_.SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℝ) (m := (d + 2, 0)) (n := 0)
        le_rfl le_rfl g x
  exact (integral_norm_le_of_polynomial_window_mass ν C d hν _ g.continuous.aestronglyMeasurable _
    (mul_nonneg (by positivity) (apply_nonneg _ _)) hb).1

/-- The regularized finite-Hecke critical-line density converges on every real Schwartz
test to the sum of all central test moments with full analytic orders. A single eventual
polynomial bound on its unit-window masses suffices. -/
theorem tendsto_integral_criticalFiniteHeckeL_schwartz_of_window_bound (χ : PontryaginDual C𝔽)
    (C : ℝ≥0) (d : ℕ)
    (hwin : ∀ᶠ η : ℝ in 𝓝[>] 0, ∀ k : ℤ, (∫ t in Icc (k : ℝ) (k + 1), density(χ, η) t) ≤
      (C : ℝ) * (1 + |(k : ℝ)|) ^ d) (g : 𝓢(ℝ, ℝ)) :
    Summable (fun z : central(χ) ↦ (mult(χ, z) : ℝ) * |g z.val.im|) ∧
    Tendsto (fun η : ℝ ↦ ∫ t, g t * density(χ, η) t) (𝓝[>] 0)
      (𝓝 (∑' z : central(χ), (mult(χ, z) : ℝ) * g z.val.im)) := by
  let ν := criticalHeckeZeroMeasure χ
  let μ := criticalHeckeDensityMeasure χ
  let D : ℝ≥0 := 3 * 2 ^ d * C
  have hD : (D : ℝ) = 3 * 2 ^ d * (C : ℝ) := by simp [D]
  have hC : (C : ℝ) ≤ D := by
    rw [hD]
    have hd : (1 : ℝ) ≤ 2 ^ d := one_le_pow₀ (by norm_num)
    calc
      _ = 1 * (C : ℝ) := (one_mul _).symm
      _ ≤ _ := mul_le_mul_of_nonneg_right (by linarith) C.coe_nonneg
  have hm : ∀ᶠ η : ℝ in 𝓝[>] 0, ∀ k : ℤ, μ η (Icc (k : ℝ) (k + 1)) ≤
      ENNReal.ofReal ((C : ℝ) * (1 + |(k : ℝ)|) ^ d) := by
    filter_upwards [hwin, self_mem_nhdsWithin] with η h hη k
    exact (criticalHeckeDensityMeasure_window χ hη k).trans_le (ENNReal.ofReal_le_ofReal (h k))
  have hcomp (f : 𝓢(ℝ, ℝ)) (hc : HasCompactSupport (f : ℝ → ℝ)) :=
    criticalHeckeDensityMeasure_compact χ f f.continuous hc
  have hn (k : ℤ) : ν (Icc (k : ℝ) (k + 1)) ≤ ENNReal.ofReal ((D : ℝ) * (1 + |(k : ℝ)|) ^ d) := by
    rw [hD]
    exact polynomial_window_mass_of_tendsto_compact _ μ ν C d hm hcomp k
  have hi := integrable_schwartz_of_criticalWindow ν D d hn g
  have hs := hasSum_criticalHeckeZeroMeasure χ g hi
  simp only [smul_eq_mul] at hs
  have habs := (show Integrable g (Measure.sum (fun z : central(χ) ↦
    (mult(χ, z) : ℝ≥0∞) • Measure.dirac z.val.im)) from hi).summable_of_dirac
  refine ⟨by simpa only [ENNReal.toReal_natCast, Real.norm_eq_abs] using habs, ?_⟩
  rw [hs.tsum_eq]
  have hlim := tendsto_integral_schwartz_of_polynomial_window_mass _ μ ν D d
    (hm.mono fun η hh k ↦ (hh k).trans (ENNReal.ofReal_le_ofReal
      (mul_le_mul_of_nonneg_right hC (by positivity)))) hn hcomp g
  apply hlim.congr'
  filter_upwards [self_mem_nhdsWithin (a := (0 : ℝ)) (s := Ioi 0)] with η hη
  change (∫ t, g t ∂criticalHeckeDensityMeasure χ η) = _
  rw [criticalHeckeDensityMeasure_pairing χ hη]
  exact integral_congr_ae (ae_of_all _ fun t ↦ mul_comm _ _)

/-- A smooth compactly supported log-profile gives precisely the centered Laplace moments
of the complex central sites. The regularized integral uses only the real vertical trace. -/
theorem tendsto_integral_criticalFiniteHeckeL_centeredLaplace_of_window_bound (χ : PontryaginDual C𝔽)
    (C : ℝ≥0) (d : ℕ)
    (hwin : ∀ᶠ η : ℝ in 𝓝[>] 0, ∀ k : ℤ, (∫ t in Icc (k : ℝ) (k + 1), density(χ, η) t) ≤
      (C : ℝ) * (1 + |(k : ℝ)|) ^ d)
    (H : ℝ → ℂ) (hH : ContDiff ℝ ∞ H) (hHc : HasCompactSupport H) :
    Summable (fun z : central(χ) ↦ (mult(χ, z) : ℝ) * |(bilateralLaplace H (z.val - 1 / 2)).re|) ∧
    Tendsto (fun η : ℝ ↦ ∫ t : ℝ, (bilateralLaplace H ((t : ℂ) * I)).re * density(χ, η) t)
      (𝓝[>] 0) (𝓝 (∑' z : central(χ), (mult(χ, z) : ℝ) * (bilateralLaplace H (z.val - 1 / 2)).re)) := by
  obtain ⟨g, hg⟩ := exists_realSchwartz_eq_bilateralLaplace_axis_re hHc hH
  have hz (z : central(χ)) : (z.val.im : ℂ) * I = z.val - 1 / 2 := by
    linear_combination criticalLine_rebuild z.val z.property.2
  simpa only [hg, hz] using tendsto_integral_criticalFiniteHeckeL_schwartz_of_window_bound χ C d hwin g

end CriticalSchwartzDensity

section ActualHeckeWindows

open Complex Filter MeasureTheory NumberField Set Topology
open scoped NNReal

local notation "cl(" t ")" => ((1 / 2 : ℂ) + ((t : ℝ) : ℂ) * I)
local notation "W(" j ")" => Icc ((j : ℤ) : ℝ) ((j : ℝ) + 1)
local notation "D(" χ ", " η ")" => analyticZeroDensity (criticalFiniteHeckeL χ) η

/-- The density is nonnegative for all nonnegative regularization parameters. -/
theorem criticalFiniteHeckeL_density_nonneg (χ : PontryaginDual C𝔽) {η : ℝ} (hη : 0 ≤ η) (t : ℝ) :
    0 ≤ D(χ, η) t := by unfold analyticZeroDensity; positivity

private theorem density_le_inverse_parameter (f : ℝ → ℂ) {η : ℝ} (hη : 0 < η) (t : ℝ) :
    analyticZeroDensity f η t ≤ 1 / (Real.pi * η) := by
  unfold analyticZeroDensity
  apply div_le_of_le_mul₀ (by positivity) (by positivity)
  calc
    _ = 1 / (Real.pi * η) * (η ^ 2 * ‖deriv f t‖ ^ 2) := by
      field_simp [Real.pi_ne_zero, hη.ne']
    _ ≤ _ := mul_le_mul_of_nonneg_left (le_add_of_nonneg_left (sq_nonneg _)) (by positivity)

private theorem criticalDensity_integrableOn (χ : PontryaginDual C𝔽) {η : ℝ} (hη : 0 < η) (j : ℤ) :
    IntegrableOn D(χ, η) W(j) := by
  have hc : IntegrableOn (fun _ : ℝ ↦ 1 / (Real.pi * η)) W(j) := integrableOn_const (by simp)
  apply hc.mono' (criticalFiniteHeckeL_density_measurable χ η).aestronglyMeasurable
  filter_upwards with t
  rw [Real.norm_of_nonneg (criticalFiniteHeckeL_density_nonneg χ hη.le t)]
  exact density_le_inverse_parameter _ hη t

private theorem density_eq_regularizedSquare {f : ℝ → ℂ} {η t : ℝ} (ht : f t ≠ 0) :
    analyticZeroDensity f η t = Real.pi⁻¹ *
      (η * (‖deriv f t‖ / ‖f t‖) ^ 2 / (1 + η ^ 2 * (‖deriv f t‖ / ‖f t‖) ^ 2)) := by
  have ha : 0 < ‖f t‖ := norm_pos_iff.mpr ht
  have hb : 0 < ‖f t‖ ^ 2 + η ^ 2 * ‖deriv f t‖ ^ 2 := by positivity
  have hc : 0 < 1 + η ^ 2 * (‖deriv f t‖ / ‖f t‖) ^ 2 := by positivity
  unfold analyticZeroDensity
  field_simp [Real.pi_ne_zero, ha.ne', hb.ne', hc.ne']

private theorem criticalRelativeDerivative (χ : PontryaginDual C𝔽) (L : ℂ → ℂ)
    (hL : MeromorphicNFOn L univ) (he : ∀ z : {z : ℂ // 1 < z.re}, L z = finiteHeckeL χ z)
    (t : ℝ) (hn : L ⟨1 / 2, t⟩ ≠ 0) :
    criticalFiniteHeckeL χ t ≠ 0 ∧
      ‖deriv (criticalFiniteHeckeL χ) t‖ / ‖criticalFiniteHeckeL χ t‖ = ‖logDeriv L ⟨1 / 2, t⟩‖ := by
  have hcl : cl(t) = (⟨1 / 2, t⟩ : ℂ) := by
    apply Complex.ext <;> norm_num [Complex.mul_re, Complex.mul_im]
  rw [← hcl] at hn ⊢
  have hnf := hL (mem_univ cl(t))
  have ha := hnf.meromorphicOrderAt_nonneg_iff_analyticAt.mp
    (hnf.meromorphicOrderAt_eq_zero_iff.mpr hn).ge
  have hp : HasDerivAt (fun u : ℝ ↦ cl(u)) I t := by
    simpa using ((Complex.ofRealCLM.hasDerivAt (x := t)).mul_const I).const_add (1 / 2 : ℂ)
  have hd := ha.differentiableAt.hasDerivAt.scomp (h := fun u : ℝ ↦ cl(u)) t hp
  rw [criticalFiniteHeckeL_eq_continuation χ L hL he]
  refine ⟨hn, ?_⟩
  change ‖deriv (L ∘ (fun u : ℝ ↦ cl(u))) t‖ / ‖L cl(t)‖ = _
  rw [hd.deriv, logDeriv_apply, norm_div]
  simp [smul_eq_mul]

private theorem criticalDensity_high_windows (χ : PontryaginDual C𝔽) :
    ∃ A > (0 : ℝ), ∃ J > (0 : ℝ), ∀ j : ℤ, J ≤ |(j : ℝ)| →
      ∀ η : ℝ, 0 < η → η ≤ 1 →
        ∫ t in W(j), D(χ, η) t ≤ A * (1 + |(j : ℝ)|) ^ 2 := by
  classical
  obtain ⟨L, hL, he⟩ := finiteHeckeL_exists_continuation χ
  obtain ⟨C, hC, J, hJ, hwindow⟩ := finiteHeckeL_continuation_highHeight_unitWindow_logDeriv χ L hL he
  let A := Real.pi⁻¹ * (4 + 2 * Real.pi) * C ^ 2
  refine ⟨A, by dsimp [A]; positivity, J, hJ, ?_⟩
  intro j hj η hη hη'
  obtain ⟨_, _, S, _, horder, hmass, _, hrect⟩ := hwindow (j : ℝ) hj
  let f := criticalFiniteHeckeL χ
  let q (t : ℝ) := ‖deriv f t‖ / ‖f t‖
  let m := analyticOrderNatAt L
  let B := C * Real.log (2 + |(j : ℝ)|)
  have hf : Continuous f := continuous_iff_continuousAt.mpr fun t ↦
    (criticalFiniteHeckeL_order χ t).1.continuousAt
  have hd : Continuous (deriv f) := continuous_iff_continuousAt.mpr fun t ↦
    (criticalFiniteHeckeL_order χ t).1.deriv.continuousAt
  have hq : Measurable q := hd.measurable.norm.div hf.measurable.norm
  have hgood : ∀ᵐ t ∂volume.restrict W(j), f t ≠ 0 ∧ 0 ≤ q t ∧
      q t ≤ B + ∑ ρ ∈ S, (m ρ : ℝ) / |t - ρ.im| := by
    have hne : ∀ᵐ t ∂volume.restrict W(j), ∀ ρ ∈ S, t ≠ ρ.im :=
      S.eventually_all.mpr (fun ρ _ ↦ ae_restrict_of_ae (volume.ae_ne ρ.im))
    filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Icc, hne] with t ht ha
    have hz := (hrect (1 / 2) ⟨le_rfl, by norm_num⟩ t ht ha).2
    have hder := criticalRelativeDerivative χ L hL he t hz.1
    exact ⟨hder.1, div_nonneg (norm_nonneg _) (norm_nonneg _), hder.2.le.trans hz.2⟩
  have hraw := integral_regularizedSquare_Icc_le_uniform S Complex.im m (j : ℝ) B η hη hη' q
    hq.aemeasurable (hgood.mono fun _ ht ↦ ht.2)
  have heq : (∫ t in W(j), D(χ, η) t) =
      Real.pi⁻¹ * ∫ t in W(j), η * (q t) ^ 2 / (1 + η ^ 2 * (q t) ^ 2) := by
    rw [← integral_const_mul]
    exact integral_congr_ae (hgood.mono fun _ ht ↦ density_eq_regularizedSquare ht.1)
  have hcard : (S.card : ℝ) ≤ ∑ ρ ∈ S, (m ρ : ℝ) := by
    calc
      _ = ∑ _ρ ∈ S, (1 : ℝ) := by simp
      _ ≤ _ := Finset.sum_le_sum fun ρ hρ ↦ by exact_mod_cast (horder ρ hρ).1
  have hB₀ : 0 ≤ B := (Finset.sum_nonneg fun ρ (_ : ρ ∈ S) ↦ (Nat.cast_nonneg (m ρ) : (0 : ℝ) ≤ _)).trans hmass
  have hprod := mul_le_mul hmass (hcard.trans hmass) (Nat.cast_nonneg S.card) hB₀
  have hrhs : 4 * B ^ 2 + 2 * Real.pi * (∑ ρ ∈ S, (m ρ : ℝ)) * S.card ≤
      (4 + 2 * Real.pi) * B ^ 2 := by
    nlinarith only [mul_le_mul_of_nonneg_left hprod (by positivity : (0 : ℝ) ≤ 2 * Real.pi)]
  have hlog : Real.log (2 + |(j : ℝ)|) ≤ 1 + |(j : ℝ)| := by
    linarith [Real.log_le_sub_one_of_pos (by positivity : 0 < 2 + |(j : ℝ)|)]
  have hbig := pow_le_pow_left₀ hB₀ (mul_le_mul_of_nonneg_left hlog hC.le) 2
  calc
    _ = _ := heq
    _ ≤ Real.pi⁻¹ * ((4 + 2 * Real.pi) * B ^ 2) :=
      mul_le_mul_of_nonneg_left (hraw.trans hrhs) (by positivity)
    _ ≤ Real.pi⁻¹ * ((4 + 2 * Real.pi) * (C * (1 + |(j : ℝ)|)) ^ 2) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hbig (by positivity)) (by positivity)
    _ = _ := by dsimp [A]; ring

private theorem criticalDensity_bounded_windows (χ : PontryaginDual C𝔽) {J : ℝ} (hJ : 0 < J) :
    ∃ M > (0 : ℝ), ∀ j : ℤ, |(j : ℝ)| < J → ∀ η : ℝ, 0 < η → ∫ t in W(j), D(χ, η) t ≤ M := by
  let b : ContDiffBump (0 : ℝ) := ⟨J + 1, J + 2, by linarith, by linarith⟩
  have hone (j : ℤ) (hj : |(j : ℝ)| < J) (t : ℝ) (ht : t ∈ W(j)) : b t = 1 := by
    apply b.one_of_mem_closedBall
    change |t - 0| ≤ J + 1
    rw [sub_zero]
    obtain ⟨hleft, hright⟩ := abs_lt.mp hj
    exact abs_le.mpr ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have hbi (η : ℝ) (hη : 0 < η) : Integrable (fun t ↦ b t * D(χ, η) t) := by
    apply ((b.continuous.integrable_of_hasCompactSupport b.hasCompactSupport).mul_const
      (1 / (Real.pi * η))).mono' (b.continuous.measurable.mul
        (criticalFiniteHeckeL_density_measurable χ η)).aestronglyMeasurable
    filter_upwards with t
    change ‖b t * D(χ, η) t‖ ≤ b t * (1 / (Real.pi * η))
    rw [Real.norm_of_nonneg (mul_nonneg (b.nonneg' t) (criticalFiniteHeckeL_density_nonneg χ hη.le t))]
    exact mul_le_mul_of_nonneg_left (density_le_inverse_parameter _ hη t) (b.nonneg' t)
  have htest (j : ℤ) (hj : |(j : ℝ)| < J) (η : ℝ) (hη : 0 < η) :
      ∫ t in W(j), D(χ, η) t ≤ ∫ t, b t * D(χ, η) t := by
    calc
      _ = ∫ t in W(j), b t * D(χ, η) t := by
        apply setIntegral_congr_fun measurableSet_Icc
        intro t ht
        change D(χ, η) t = b t * D(χ, η) t
        rw [hone j hj t ht, one_mul]
      _ ≤ _ := setIntegral_le_integral (hbi η hη) (ae_of_all _ fun t ↦
        mul_nonneg (b.nonneg' t) (criticalFiniteHeckeL_density_nonneg χ hη.le t))
  obtain ⟨M, hM⟩ : ∃ M : ℝ, ∀ᶠ η : ℝ in 𝓝[>] 0, (∫ t, b t * D(χ, η) t) ≤ M := by
    have hlim := tendsto_integral_criticalFiniteHeckeL χ b.continuous b.hasCompactSupport
    exact ⟨_, hlim.eventually_le_const (lt_add_one _)⟩
  obtain ⟨δ, hδ, hsmall⟩ := (nhdsGT_basis (0 : ℝ)).eventually_iff.mp hM
  refine ⟨max M (1 / (Real.pi * δ)), (by positivity : 0 < 1 / (Real.pi * δ)).trans_le
    (le_max_right _ _), ?_⟩
  intro j hj η hη
  by_cases hs : η < δ
  · exact (htest j hj η hη).trans ((hsmall ⟨hη, hs⟩).trans (le_max_left _ _))
  · apply le_trans _ (le_max_right _ _)
    have hc : IntegrableOn (fun _ : ℝ ↦ 1 / (Real.pi * η)) W(j) := integrableOn_const (by simp)
    calc
      _ ≤ ∫ _t in W(j), 1 / (Real.pi * η) := integral_mono (criticalDensity_integrableOn χ hη j) hc
        (density_le_inverse_parameter _ hη)
      _ = 1 / (Real.pi * η) := by simp [measureReal_def, Real.volume_Icc]
      _ ≤ _ := one_div_le_one_div_of_le (mul_pos Real.pi_pos hδ)
        (mul_le_mul_of_nonneg_left (le_of_not_gt hs) Real.pi_pos.le)

/-- One quadratic bound controls the regularized finite Hecke density on every
integer unit window simultaneously for every parameter in `(0, 1]`. -/
theorem criticalFiniteHeckeL_polynomial_window_mass (χ : PontryaginDual C𝔽) :
    ∃ C : ℝ≥0, ∀ η : ℝ, 0 < η → η ≤ 1 → ∀ j : ℤ,
      IntegrableOn D(χ, η) W(j) ∧
        ∫ t in W(j), D(χ, η) t ≤ (C : ℝ) * (1 + |(j : ℝ)|) ^ 2 := by
  obtain ⟨A, hA, J, hJ, hhigh⟩ := criticalDensity_high_windows χ
  obtain ⟨M, hM, hlow⟩ := criticalDensity_bounded_windows χ hJ
  refine ⟨⟨max A M, hA.le.trans (le_max_left _ _)⟩, fun η hη hη' j ↦
    ⟨criticalDensity_integrableOn χ hη j, ?_⟩⟩
  change _ ≤ max A M * (1 + |(j : ℝ)|) ^ 2
  by_cases hj : J ≤ |(j : ℝ)|
  · exact (hhigh j hj η hη hη').trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (sq_nonneg _))
  · apply (hlow j (lt_of_not_ge hj) η hη).trans
    have hOne := one_le_pow₀ (show 1 ≤ 1 + |(j : ℝ)| by linarith [abs_nonneg (j : ℝ)]) (n := 2)
    exact (le_max_right A M).trans (le_mul_of_one_le_right (hM.le.trans (le_max_right _ _)) hOne)

/-- The simultaneous window bound in the form used to extend compact-test
convergence to Schwartz tests by polynomial mass control. -/
theorem criticalFiniteHeckeL_eventually_polynomial_window_mass (χ : PontryaginDual C𝔽) :
    ∃ C : ℝ≥0, ∀ᶠ η : ℝ in 𝓝[>] 0, ∀ j : ℤ, IntegrableOn D(χ, η) W(j) ∧
      ∫ t in W(j), D(χ, η) t ≤ (C : ℝ) * (1 + |(j : ℝ)|) ^ 2 := by
  obtain ⟨C, hC⟩ := criticalFiniteHeckeL_polynomial_window_mass χ
  refine ⟨C, ?_⟩
  have hnear : Tendsto (fun η : ℝ ↦ η) (𝓝[>] 0) (𝓝 0) := tendsto_id.mono_left nhdsWithin_le_nhds
  have hpos : ∀ᶠ η : ℝ in 𝓝[>] 0, 0 < η := self_mem_nhdsWithin
  filter_upwards [hpos, hnear.eventually_le_const (by norm_num : (0 : ℝ) < 1)] with η hη hη'
  exact hC η hη hη'

end ActualHeckeWindows

section CriticalSchwartzLimits

open Complex Filter MeasureTheory NumberField Set Topology
open scoped _root_.SchwartzMap ContDiff

local notation "ord(" χ ", " z ")" => MeromorphicOn.divisor (continuedCompletedHeckeL (F := F) χ) univ z
local notation "central(" χ ")" => {z : ℂ // 0 < ord(χ, z) ∧ Complex.re z = 1 / 2}
local notation "mult(" χ ", " z ")" => Int.toNat (ord(χ, (z : ℂ)))
local notation "density(" χ ", " η ")" => analyticZeroDensity (criticalFiniteHeckeL χ) η

/-- For every Hecke character, the whole-line regularized integral recovers the
absolutely summable central moments of every real Schwartz test. -/
theorem tendsto_integral_criticalFiniteHeckeL_schwartz (χ : PontryaginDual C𝔽) (g : 𝓢(ℝ, ℝ)) :
    Summable (fun z : central(χ) ↦ (mult(χ, z) : ℝ) * |g z.val.im|) ∧
    Tendsto (fun η : ℝ ↦ ∫ t, g t * density(χ, η) t) (𝓝[>] 0)
      (𝓝 (∑' z : central(χ), (mult(χ, z) : ℝ) * g z.val.im)) := by
  obtain ⟨C, hC⟩ := criticalFiniteHeckeL_eventually_polynomial_window_mass χ
  exact tendsto_integral_criticalFiniteHeckeL_schwartz_of_window_bound χ C 2
    (hC.mono fun _ hk k ↦ (hk k).2) g

/-- On a smooth compactly supported log-profile the regularized finite-Hecke density
recovers the full central real moments of its centered bilateral Laplace transform. -/
theorem tendsto_integral_criticalFiniteHeckeL_centeredLaplace (χ : PontryaginDual C𝔽)
    (H : ℝ → ℂ) (hH : ContDiff ℝ ∞ H) (hHc : HasCompactSupport H) :
    Summable (fun z : central(χ) ↦ (mult(χ, z) : ℝ) * |(bilateralLaplace H (z.val - 1 / 2)).re|) ∧
    Tendsto (fun η : ℝ ↦ ∫ t : ℝ, (bilateralLaplace H ((t : ℂ) * I)).re * density(χ, η) t)
      (𝓝[>] 0) (𝓝 (∑' z : central(χ), (mult(χ, z) : ℝ) * (bilateralLaplace H (z.val - 1 / 2)).re)) := by
  obtain ⟨C, hC⟩ := criticalFiniteHeckeL_eventually_polynomial_window_mass χ
  exact tendsto_integral_criticalFiniteHeckeL_centeredLaplace_of_window_bound χ C 2
    (hC.mono fun _ hk k ↦ (hk k).2) H hH hHc

end CriticalSchwartzLimits

section CriticalHeckeLattice

open Complex Filter Metric Topology
open RiemannMasullo.AnalyticLattice
open scoped _root_.SchwartzMap

local notation "cl(" t ")" => ((1 / 2 : ℂ) + ((t : ℝ) : ℂ) * I)
local notation "ord(" χ ", " z ")" =>
  MeromorphicOn.divisor (continuedCompletedHeckeL (F := F) χ) univ z
local notation "central(" χ ")" => {z : ℂ // 0 < ord(χ, z) ∧ Complex.re z = 1 / 2}

/-- The logarithmic window estimate for the finite Hecke continuation bounds the actual
normalized count of strict consecutive-value comparisons in each high integer bin. -/
theorem criticalFiniteHeckeL_high_bin_count (χ : PontryaginDual C𝔽) :
    ∃ C > (0 : ℝ), ∃ J > (0 : ℝ), ∀ j : ℤ, J ≤ |(j : ℝ)| → ∀ n : ℕ, 0 < n →
      ((binIndices (criticalFiniteHeckeL χ) j n).card : ℝ) / n ≤
        13 * (C * Real.log (2 + |(j : ℝ)|) + 1) ^ 2 := by
  let L := (finiteHeckeL_exists_continuation χ).choose
  obtain ⟨hL, he⟩ := (finiteHeckeL_exists_continuation χ).choose_spec
  have hfinite := criticalFiniteHeckeL_eq_continuation χ L hL he
  obtain ⟨C, hC, J, hJ, hrect⟩ := finiteHeckeL_continuation_highHeight_unitWindow_logDeriv χ L hL he
  refine ⟨C, hC, J, hJ, ?_⟩
  intro j hj n hn
  obtain ⟨hA, _, S, _, horders, hmass, _, hw⟩ := hrect j hj
  apply bin_count_le_of_logDeriv S (analyticOrderNatAt L) Complex.im
    (mul_nonneg hC.le (Real.log_nonneg (by linarith [abs_nonneg (j : ℝ)])))
    (fun z hz ↦ (horders z hz).1) hmass j _ n hn
  intro t ht hne
  obtain ⟨_, hval, hder⟩ := hw (1 / 2 : ℝ) ⟨le_rfl, by norm_num⟩ t ht hne
  have hm : cl(t) = (⟨1 / 2, t⟩ : ℂ) := by apply Complex.ext <;> simp
  have hzin : cl(t) ∈ closedBall (⟨2, (j : ℝ) + 1 / 2⟩ : ℂ) 4 := by
    rw [mem_closedBall, dist_eq_norm, hm]
    apply (Complex.norm_le_abs_re_add_abs_im _).trans
    change |1 / 2 - 2| + |t - ((j : ℝ) + 1 / 2)| ≤ 4
    have hbound : |t - ((j : ℝ) + 1 / 2)| ≤ 1 / 2 := abs_le.mpr ⟨by linarith [ht.1], by linarith [ht.2]⟩
    norm_num
    linarith
  have hp : HasDerivAt (fun u : ℝ ↦ cl(u)) I t := by
    simpa using ((Complex.ofRealCLM.hasDerivAt (x := t)).mul_const I).const_add (1 / 2 : ℂ)
  have hd := (hA _ hzin).differentiableAt.hasDerivAt.scomp (h := fun u : ℝ ↦ cl(u)) t hp
  rw [hfinite]
  refine ⟨by change L cl(t) ≠ 0; rw [hm]; exact hval, hd.differentiableAt, ?_⟩
  change ‖deriv (L ∘ fun u : ℝ ↦ cl(u)) t‖ / ‖L cl(t)‖ ≤ _
  rw [hd.deriv, hm]
  simpa [logDeriv, smul_eq_mul, norm_div] using hder

/-- The compact strict lattice probe of the finite Hecke function recovers the occupied
critical-line divisor with its full orders. -/
theorem tendsto_sampleSum_criticalFiniteHeckeL_compact (χ : PontryaginDual C𝔽) {g : ℝ → ℝ}
    (hg : Continuous g) (hgc : HasCompactSupport g) :
    Tendsto (sampleSum (criticalFiniteHeckeL χ) g) atTop
      (𝓝 (∑' z : central(χ), ((ord(χ, z.val)).toNat : ℝ) * g z.val.im)) := by
  classical
  let f := criticalFiniteHeckeL χ
  let C := {z : ℂ // 0 < ord(χ,z) ∧ z.re = 1/2}
  have hlocal (t : ℝ) := criticalFiniteHeckeL_order χ t
  have hfin (t : ℝ) : analyticOrderAt f t ≠ ⊤ := fun ht ↦ (hlocal t).2.1 (analyticOrderAt_eq_top.mp ht)
  have hlim := tendsto_sampleSum (f := f) hg hgc (fun t _ ↦ (hlocal t).1) (fun t _ ↦ hfin t)
  have hsum := critical_zero_moments_eq χ g
  change Tendsto (sampleSum f g) atTop (𝓝 (∑' z : C, ((ord(χ, z.val)).toNat : ℝ) * g z.val.im))
  rw [← hsum]
  exact hlim

/-- The finite Hecke continuation's strict lattice probe converges against every real
Schwartz function to the genuine completed central divisor, including all multiplicities. -/
theorem tendsto_sampleSum_criticalFiniteHeckeL (χ : PontryaginDual C𝔽) (g : 𝓢(ℝ, ℝ)) :
    Tendsto (sampleSum (criticalFiniteHeckeL χ) g) atTop
      (𝓝 (∑' z : central(χ), ((ord(χ, z.val)).toNat : ℝ) * g z.val.im)) := by
  classical
  let Z := {z : ℂ // 0 < ord(χ, z)}
  let e (z : central(χ)) : Z := ⟨z.val, z.2.1⟩
  have he : Function.Injective e := fun _ _ h ↦ Subtype.ext (congrArg (fun z : Z ↦ z.val) h)
  have hZ : Summable (fun z : Z ↦ (ord(χ, z.val) : ℝ) / (1 + |z.val.im|) ^ 2) := by
    simpa only [explicitFormulaCompletedHeckeL, continuedCompletedHeckeL] using
      explicitFormulaCompletedHeckeL_summable_divisor_div_sq χ
  have hc : Summable (fun z : central(χ) ↦ ((ord(χ, z.val)).toNat : ℝ) / (1 + |z.val.im|)^2) := by
    apply (hZ.comp_injective he).congr
    intro z
    change (ord(χ, z.val) : ℝ) / _ = _
    have hcast : ((ord(χ, z.val)).toNat : ℝ) = (ord(χ, z.val) : ℝ) := by
      exact_mod_cast Int.toNat_of_nonneg z.2.1.le
    rw [hcast]
  obtain ⟨C, hC, J, hJ, hhigh⟩ := criticalFiniteHeckeL_high_bin_count χ
  apply tendsto_sampleSum_schwartz (criticalFiniteHeckeL χ) (fun z : central(χ) ↦ z.val.im)
    (fun z ↦ ((ord(χ, z.val)).toNat : ℝ)) (fun _ ↦ Nat.cast_nonneg _) hc
    (fun _ ↦ tendsto_sampleSum_criticalFiniteHeckeL_compact χ)
    (C := 13 * (C + 1)^2) (J := J) (by positivity) _ g
  intro j hj n hn
  have hl : Real.log (2 + |(j : ℝ)|) ≤ 1 + |(j : ℝ)| := by
    linarith [Real.log_le_sub_one_of_pos (show 0 < 2 + |(j : ℝ)| by positivity)]
  have hlog : 0 ≤ Real.log (2 + |(j : ℝ)|) := Real.log_nonneg (by linarith [abs_nonneg (j : ℝ)])
  have hsize : C * Real.log (2 + |(j : ℝ)|) + 1 ≤ (C+1) * (1+|(j : ℝ)|) := by
    nlinarith [mul_le_mul_of_nonneg_left hl hC.le, abs_nonneg (j : ℝ)]
  calc
    _ ≤ _ := hhigh j hj n hn
    _ ≤ 13 * ((C+1) * (1+|(j : ℝ)|))^2 :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hsize 2) (by norm_num)
    _ = _ := by ring

/-- The normalized character's chosen continuation is sampled directly at the prescribed
critical-line points on every mesh. -/
theorem tendsto_sampleSum_chosenFiniteHeckeL
    (τ : ℝ≥0ˣ →ₜ* C𝔽) (χ : {χ : PontryaginDual C𝔽 // ∀ a : ℝ≥0ˣ, χ (τ a) = 1})
    (g : 𝓢(ℝ, ℝ)) :
    let L := (finiteHeckeL_exists_continuation χ.val).choose
    Tendsto (sampleSum (fun t : ℝ ↦ L cl(t)) g) atTop
      (𝓝 (∑' z : central(χ.val), ((ord(χ.val, z.val)).toNat : ℝ) * g z.val.im)) := by
  let L := (finiteHeckeL_exists_continuation χ.val).choose
  have hL := (finiteHeckeL_exists_continuation χ.val).choose_spec
  change Tendsto (sampleSum (fun t : ℝ ↦ L cl(t)) g) atTop _
  rw [← criticalFiniteHeckeL_eq_continuation χ.val L hL.1 hL.2]
  exact tendsto_sampleSum_criticalFiniteHeckeL χ.val g

open Function PolynomialIdealSamples

/-- The observed critical-line magnitudes from the polynomial-length ideal sum. -/
def polynomialIdealSampleMagnitude : PontryaginDual C𝔽 → ℕ → ℤ → ℝ :=
  open scoped RiemannMasullo.Isolated.criticalFiniteHeckeL in
  fun (χ : PontryaginDual C𝔽) (n : ℕ) (k : ℤ) ↦ ‖frequencySample χ n (samplePoint n k)‖

/-- The actual successor-inclusive finite grid has every prescribed enclosure
for all sufficiently large meshes. -/
theorem eventuallyAccurate_polynomialIdealSampleMagnitude (τ : ℝ≥0ˣ →ₜ* C𝔽) (hτ : RightInverse τ (ideleClassNorm F))
    (χ : PontryaginDual C𝔽) (hχ : ∀ t, χ (τ t)=1) :
    EventuallyAccurateMagnitudes (criticalFiniteHeckeL χ) (polynomialIdealSampleMagnitude χ) := by
  obtain ⟨L,hL,he⟩ := finiteHeckeL_exists_continuation χ
  rw [criticalFiniteHeckeL_eq_continuation χ L hL he]
  filter_upwards [eventually_frequencySample_error τ hτ χ hχ L hL he,eventually_gt_atTop (0:ℕ)]
    with n hn hn₀
  intro k hk
  let t := samplePoint n k
  have ht : |t| ≤ (n:ℝ)+1 := abs_samplePoint_le_succ hn₀ hk
  have hz : (1/2:ℂ)+(t:ℂ)*I = point t := by
    apply Complex.ext <;> norm_num [point,Complex.mul_re,Complex.mul_im]
  rw [sampleError_eq_pow]
  change |‖frequencySample χ n t‖-‖L ((1/2:ℂ)+(t:ℂ)*I)‖| ≤ _
  rw [abs_sub_comm,hz]
  exact (abs_norm_sub_norm_le _ _).trans (hn t ht).le

/-- The same strict finite observation recovers the full central divisor
with orders for every nonnegative real Schwartz test. -/
theorem tendsto_certified_polynomialIdealSampleMagnitude (τ : ℝ≥0ˣ →ₜ* C𝔽) (hτ : RightInverse τ (ideleClassNorm F))
    (χ : PontryaginDual C𝔽) (hχ : ∀ t, χ (τ t)=1) (g : 𝓢(ℝ,ℝ)) (hg : ∀ t, 0 ≤ g t) :
    (∀ᶠ n : ℕ in atTop, certifiedSum (polynomialIdealSampleMagnitude χ) g n ≤ sampleSum (criticalFiniteHeckeL χ) g n) ∧
    Tendsto (certifiedSum (polynomialIdealSampleMagnitude χ) g) atTop
      (𝓝 (∑' z : central(χ), ((ord(χ,z.val)).toNat : ℝ)*g z.val.im)) := by
  have ho (t : ℝ) := criticalFiniteHeckeL_order χ t
  exact tendsto_certifiedSum_of_eventuallyAccurate (eventuallyAccurate_polynomialIdealSampleMagnitude τ hτ χ hχ)
    (fun t ↦ (ho t).1) (fun t h ↦ (ho t).2.1 (analyticOrderAt_eq_top.mp h))
    (fun z : central(χ) ↦ z.val.im) (fun z ↦ ((ord(χ,z.val)).toNat : ℝ))
    (fun _ ↦ Nat.cast_nonneg _) (fun _ ↦ tendsto_sampleSum_criticalFiniteHeckeL_compact χ)
    g.continuous hg (tendsto_sampleSum_criticalFiniteHeckeL χ g)

end CriticalHeckeLattice

section CriticalMeasurements

open Complex Filter Function IsDedekindDomain
open scoped _root_.SchwartzMap Topology

local notation "ord(" χ ", " z ")" => MeromorphicOn.divisor (continuedCompletedHeckeL (F := F) χ) univ z
local notation "Chars(" τ ")" => {χ : PontryaginDual C𝔽 // ∀ t : ℝ≥0ˣ, χ (τ t) = 1}
local notation "Sites(" χ ")" => {z : ℂ // 0 < ord(χ,z)}
local notation "M(" φ ", " χ ", " z ")" => modulatedFourierMellin m𝔽 univ
  ⟨isProperMap_ideleClassNorm F, ideleClassNorm_ne_one (F := F)⟩ μ𝔽 (φ : BruhatCompactSupport C𝔽).val
  (ideleClassNormTwist (F := F) χ ((z : ℂ) - 1/2))
local notation "ext(" τ ", " α ")" => {p : Chars(τ) × ℂ //
  0 < ord(p.1.val,p.2) ∧ α ≤ |p.2.re-1/2|}
local notation "target(" τ ")" => (∀ (α : ℝ), 0 < α → ∀ f : BruhatCompactSupport C𝔽,
  (∀ g : C₁, f.val g = 0) → HasSum (fun p : ext(τ,α) ↦
    ((ord(p.val.1.val,p.val.2) : ℤ) : ℂ)*M(f,p.val.1.val,p.val.2)) 0)
local notation "centralMass(" χ ", " g ")" =>
  (∑' z : {z : ℂ // 0 < ord(χ,z) ∧ z.re = 1/2},
    ((ord(χ,z.val)).toNat : ℝ) * (g : ℝ → ℝ) z.val.im)

private theorem allCentral_iff_exteriorZeros (τ : ℝ≥0ˣ →ₜ* C𝔽) (hτ : RightInverse τ (ideleClassNorm F)) :
    (∀ (χ : Chars(τ)) (z : Sites(χ.val)), z.val.re = 1/2) ↔ target(τ) := by
  constructor
  · intro hc α hα
    apply (hasSum_exteriorZeros_iff_isEmpty τ hτ α).mpr
    refine ⟨fun p ↦ ?_⟩
    have hz := hc p.val.1 ⟨p.val.2,p.property.1⟩
    have he := p.property.2
    change p.val.2.re = 1/2 at hz
    rw [hz,sub_self,abs_zero] at he
    exact hα.not_ge he
  · intro h χ z
    by_contra hne
    have ha : 0 < |z.val.re-1/2| := abs_pos.mpr (sub_ne_zero.mpr hne)
    have h₀ := (hasSum_exteriorZeros_iff_isEmpty τ hτ _).mp (h _ ha)
    exact h₀.false ⟨(χ,z.val),z.property,le_refl _⟩

private theorem lowerBound_iff_cofinal_samples {v : ℕ → ℝ} {L S : ℝ}
    (hv : Tendsto v atTop (𝓝 L)) :
    (∀ δ : ℝ, 0 < δ → ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧ S-δ ≤ v n) ↔ S ≤ L := by
  constructor
  · intro h
    by_contra! hgap
    let d := (S-L)/3
    have hd : 0 < d := by dsimp [d]; linarith
    obtain ⟨N,hN⟩ := eventually_atTop.1 (hv.eventually (gt_mem_nhds (show L < L+d by linarith)))
    obtain ⟨n,hn,hl⟩ := h d hd N
    have hh := hN n hn
    change v n < L+d at hh
    dsimp [d] at hh hl
    linarith
  · intro h δ hδ N
    obtain ⟨M,hM⟩ := eventually_atTop.1 (hv.eventually (lt_mem_nhds (show S-δ < L by linarith)))
    exact ⟨max N M,le_max_left _ _,(hM _ (le_max_right N M)).le⟩

private theorem centralMass_of_hasSum (χ : PontryaginDual C𝔽) (g : 𝓢(ℝ, ℝ))
    (W : Sites(χ) → ℝ) (S : ℝ) (hS : HasSum W S) (hpos : ∀ z, 0 < W z)
    (hline : ∀ z : Sites(χ), z.val.re = 1/2 →
      W z = ((ord(χ,z.val)).toNat : ℝ) * g z.val.im) :
    centralMass(χ,g) ≤ S ∧ (S ≤ centralMass(χ,g) ↔ ∀ z : Sites(χ), z.val.re = 1/2) := by
  classical
  let C : Set (Sites(χ)) := {z | z.val.re = 1/2}
  let D : Set (Sites(χ)) := Cᶜ
  let e : C ≃ {z : ℂ // 0 < ord(χ,z) ∧ z.re = 1/2} :=
    { toFun := fun z ↦ ⟨z.val.val, z.val.property, z.property⟩
      invFun := fun z ↦ ⟨⟨z.val, z.property.1⟩, z.property.2⟩
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl }
  have hcen : ∑' z : C, W z.val = centralMass(χ,g) := by
    rw [← e.tsum_eq]
    exact tsum_congr fun z ↦ hline z.val z.property
  have hsplit := hS.summable.tsum_subtype_add_tsum_subtype_compl C
  rw [hcen, hS.tsum_eq] at hsplit
  change centralMass(χ,g) + (∑' z : D, W z.val) = S at hsplit
  have hnon : 0 ≤ ∑' z : D, W z.val := tsum_nonneg fun z ↦ (hpos z.val).le
  refine ⟨by linarith, ?_⟩
  constructor
  · intro h z
    by_contra hz
    have hp := (hS.summable.subtype (· ∈ D)).tsum_pos (fun j ↦ (hpos j.val).le)
      (⟨z, hz⟩ : D) (hpos z)
    change 0 < ∑' i : D, W i.val at hp
    linarith
  · intro h
    have : IsEmpty D := ⟨fun z ↦ z.property (h z.val)⟩
    simpa using hsplit.ge

local notation "grid(" χ ", " g ")" => AnalyticLattice.sampleSum (fun t : ℝ ↦
  (finiteHeckeL_exists_continuation (F := F) χ).choose ((1/2 : ℂ) + (t : ℂ)*I)) g
local notation "densityMass(" χ ", " g ")" => (limUnder (𝓝[>] (0 : ℝ))
  (fun η : ℝ ↦ ∫ t : ℝ, (g : ℝ → ℝ) t * analyticZeroDensity (criticalFiniteHeckeL χ) η t))

/-- Theorem 12.5.1.1, pp. 519–520. Suppose a real scalar is the sum of strictly positive
weights at all positive divisor sites, with prescribed Schwartz weights on the line. Then an
arbitrarily late lower comparison with the derivative-free finite Hecke samples is equivalent
to the exterior sum in the theorem at all positive widths. -/
theorem finiteCriticalSamples_iff_exteriorZeros_of_hasSum
    (τ : ℝ≥0ˣ →ₜ* C𝔽) (hτ : RightInverse τ (ideleClassNorm F)) (g : 𝓢(ℝ, ℝ))
    (W : (χ : Chars(τ)) → Sites(χ.val) → ℝ) (S : Chars(τ) → ℝ)
    (hS : ∀ χ, HasSum (W χ) (S χ)) (hpos : ∀ χ z, 0 < W χ z)
    (hline : ∀ (χ : Chars(τ)) (z : Sites(χ.val)), z.val.re = 1/2 →
      W χ z = ((ord(χ.val,z.val)).toNat : ℝ) * g z.val.im) :
    (∀ χ : Chars(τ), limUnder atTop grid(χ.val,g) ≤ S χ) ∧
      ((∀ (χ : Chars(τ)) (δ : ℝ), 0 < δ → ∀ N : ℕ,
        ∃ n : ℕ, N ≤ n ∧ S χ - δ ≤ grid(χ.val,g) n) ↔ target(τ)) := by
  have h (χ : Chars(τ)) := centralMass_of_hasSum χ.val g (W χ) (S χ) (hS χ) (hpos χ) (hline χ)
  constructor
  · intro χ
    rw [(tendsto_sampleSum_chosenFiniteHeckeL τ χ g).limUnder_eq]
    exact (h χ).1
  · refine Iff.trans ?_ (allCentral_iff_exteriorZeros τ hτ)
    apply forall_congr'
    intro χ
    exact (lowerBound_iff_cofinal_samples (tendsto_sampleSum_chosenFiniteHeckeL τ χ g)).trans (h χ).2

/-- Under the same positive full-site identity, the reverse lower comparison with the
regularized finite-Hecke integral on the critical line is equivalent to Theorem 12.5.1.1
at every positive width. The measured integral always gives a lower bound on the full sum. -/
theorem criticalDensity_iff_exteriorZeros_of_hasSum
    (τ : ℝ≥0ˣ →ₜ* C𝔽) (hτ : RightInverse τ (ideleClassNorm F)) (g : 𝓢(ℝ, ℝ))
    (W : (χ : Chars(τ)) → Sites(χ.val) → ℝ) (S : Chars(τ) → ℝ)
    (hS : ∀ χ, HasSum (W χ) (S χ)) (hpos : ∀ χ z, 0 < W χ z)
    (hline : ∀ (χ : Chars(τ)) (z : Sites(χ.val)), z.val.re = 1/2 →
      W χ z = ((ord(χ.val,z.val)).toNat : ℝ) * g z.val.im) :
    (∀ χ : Chars(τ), densityMass(χ.val,g) ≤ S χ) ∧
      ((∀ χ : Chars(τ), S χ ≤ densityMass(χ.val,g)) ↔ target(τ)) := by
  have h (χ : Chars(τ)) := centralMass_of_hasSum χ.val g (W χ) (S χ) (hS χ) (hpos χ) (hline χ)
  constructor
  · intro χ
    rw [(tendsto_integral_criticalFiniteHeckeL_schwartz χ.val g).2.limUnder_eq]
    exact (h χ).1
  · refine Iff.trans ?_ (allCentral_iff_exteriorZeros τ hτ)
    apply forall_congr'
    intro χ
    rw [(tendsto_integral_criticalFiniteHeckeL_schwartz χ.val g).2.limUnder_eq]
    exact (h χ).2
end CriticalMeasurements

/-! ## Compact circle measurements of the exterior terms -/

namespace CompactGreen

open Filter HeckePoisson HeckeHalfPlaneJensen
open scoped Topology

local notation "U𝔽" => PontryaginDual C𝔽
local notation "ord(" χ ", " z ")" =>
  MeromorphicOn.divisor (continuedCompletedHeckeL (F := F) χ) univ z
local notation "ext(" τ ", " a ")" =>
  {p : {χ : U𝔽 // ∀ u : ℝ≥0ˣ, χ (τ u) = 1} × ℂ //
    0 < ord(p.1.val, p.2) ∧ (a : ℝ) ≤ |p.2.re - 1/2|}
local notation "allWidths(" τ ")" =>
  ∀ a > (0 : ℝ), ∀ φ : BruhatCompactSupport C𝔽, (∀ g : C₁, φ.val g = 0) →
    HasSum (fun z : ext(τ, a) ↦ (ord(z.val.1.val, z.val.2) : ℂ) *
      modulatedFourierMellin m𝔽 univ ⟨isProperMap_ideleClassNorm F, ideleClassNorm_ne_one (F := F)⟩
        μ𝔽 φ.val (ideleClassNormTwist z.val.1.val (z.val.2 - 1/2))) 0

private theorem allWidths_iff_critical (τ : ℝ≥0ˣ →ₜ* C𝔽) (hτ : Function.RightInverse τ (ideleClassNorm F)) :
    allWidths(τ) ↔ ∀ χ : U𝔽, (∀ u : ℝ≥0ˣ, χ (τ u) = 1) → ∀ z : Site χ, z.val.re = 1/2 := by
  have ha : allWidths(τ) ↔ (∀ a > 0, PoissonCertificate.exteriorCancellation τ a) := by
    simp only [PoissonCertificate.exteriorCancellation,modulatedFourierMellin,relativeVerticalStrip,
      Set.preimage_univ,Set.indicator_univ]
  rw [ha,PoissonCertificate.all_widths_iff_integer_mass τ hτ]
  constructor <;> intro h χ hχ
  · exact (criticalLine_iff_integer_mass χ).mpr (h χ hχ)
  · exact (criticalLine_iff_integer_mass χ).mp (h χ hχ)

/-- Paper: Theorem 12.5.1.1, pp. 519–520. The claimed all-width exterior cancellation is
equivalent to a nonpositive limit of the genuine corrected finite-Hecke circle means
for every character normalized by the given norm section. -/
theorem all_widths_iff_circleLimit_nonpos (τ : ℝ≥0ˣ →ₜ* C𝔽)
    (hτ : Function.RightInverse τ (ideleClassNorm F)) :
    allWidths(τ) ↔ ∀ χ : U𝔽, (∀ u : ℝ≥0ˣ, χ (τ u) = 1) →
      Filter.limUnder (𝓝[<] (1 : ℝ)) (correctedMean χ (finiteHeckeL_exists_continuation χ).choose) ≤ 0 := by
  rw [allWidths_iff_critical τ hτ]
  constructor <;> intro h χ hχ
  · rw [(tendsto_corrected_circle_mean_rightGreenMass τ hτ χ hχ).2.limUnder_eq,
      (rightGreenMass_eq_zero_iff χ).mpr (h χ hχ)]
  · have hle := h χ hχ
    rw [(tendsto_corrected_circle_mean_rightGreenMass τ hτ χ hχ).2.limUnder_eq] at hle
    exact (rightGreenMass_eq_zero_iff χ).mp (le_antisymm hle (rightGreenMass_nonneg χ))

/-- Paper: Theorem 12.5.1.1, pp. 519–520. The all-width cancellation is also equivalent
to nonpositivity of each corrected compact mean, including circles passing through
a zero or the possible principal pole. -/
theorem all_widths_iff_compact_circleMeans_nonpos (τ : ℝ≥0ˣ →ₜ* C𝔽)
    (hτ : Function.RightInverse τ (ideleClassNorm F)) :
    allWidths(τ) ↔ ∀ χ : U𝔽, (∀ u : ℝ≥0ˣ, χ (τ u) = 1) → ∀ r ∈ Ioo (0 : ℝ) 1,
      correctedMean χ (finiteHeckeL_exists_continuation χ).choose r ≤ 0 := by
  rw [all_widths_iff_circleLimit_nonpos τ hτ]
  constructor
  · intro h χ hχ r hr
    have hle := h χ hχ
    rw [(tendsto_corrected_circle_mean_rightGreenMass τ hτ χ hχ).2.limUnder_eq] at hle
    exact (correctedMean_mem_Icc τ hτ χ hχ hr).2.trans hle
  · intro h χ hχ
    have ht := (tendsto_corrected_circle_mean_rightGreenMass τ hτ χ hχ).2
    rw [ht.limUnder_eq]
    apply le_of_tendsto ht
    filter_upwards [Ioo_mem_nhdsLT (by norm_num : (0 : ℝ) < 1)] with r hr
    exact h χ hχ r hr

open HeckeBoundaryGreen

private theorem criticalLogDifference_eq_mass (τ : ℝ≥0ˣ →ₜ* C𝔽) (hτ : Function.RightInverse τ (ideleClassNorm F))
    (χ : U𝔽) (hχ : ∀ u : ℝ≥0ˣ, χ (τ u) = 1) :
    criticalLogDifference χ = rightGreenMass χ :=
  (hasSum_green_criticalLogDifference τ hτ χ hχ).tsum_eq.symm

/-- Paper: Theorem 12.5.1.1, pp. 519–520. Reconstruction: the all-width exterior cancellation is
equivalent to a single upper bound for the critical-line logarithmic integral of each normalized
character. The principal-character reference includes its pole correction at one. -/
theorem all_widths_iff_criticalLogDifference_nonpos (τ : ℝ≥0ˣ →ₜ* C𝔽)
    (hτ : Function.RightInverse τ (ideleClassNorm F)) :
    allWidths(τ) ↔ ∀ χ : U𝔽, (∀ u : ℝ≥0ˣ, χ (τ u) = 1) → criticalLogDifference χ ≤ 0 := by
  rw [allWidths_iff_critical τ hτ]
  constructor
  · intro h χ hχ
    rw [criticalLogDifference_eq_mass τ hτ χ hχ, (rightGreenMass_eq_zero_iff χ).mpr (h χ hχ)]
  · intro h χ hχ
    have hh := h χ hχ
    rw [criticalLogDifference_eq_mass τ hτ χ hχ] at hh
    exact (rightGreenMass_eq_zero_iff χ).mp (le_antisymm hh (rightGreenMass_nonneg χ))

/-- Paper: Theorem 12.5.1.1, pp. 519–520. For each compact test and normalized character, the
absolute omitted Mellin sum, including both edges of any positive strip, is bounded by the
actual critical-line logarithmic difference times a test constant divided by the width. -/
theorem exists_hasSum_absolute_exterior_le_criticalLogDifference (τ : ℝ≥0ˣ →ₜ* C𝔽)
    (hτ : Function.RightInverse τ (ideleClassNorm F)) (χ : U𝔽)
    (hχ : ∀ u : ℝ≥0ˣ, χ (τ u) = 1) (φ : BruhatCompactSupport C𝔽) :
    ∃ W : ℝ, 0 ≤ W ∧ ∀ α : ℝ, 0 < α → ∃ A : ℝ,
      HasSum (fun z : {p : ℂ // 0 < ord(χ, p) ∧ α ≤ |p.re-1/2|} ↦
        ‖(ord(χ, z.val) : ℂ) *
          modulatedFourierMellin m𝔽 univ ⟨isProperMap_ideleClassNorm F, ideleClassNorm_ne_one (F := F)⟩
            μ𝔽 φ.val (ideleClassNormTwist χ (z.val - 1/2))‖) A ∧
      A ≤ (3*W/(2*α)) * criticalLogDifference χ := by
  rw [criticalLogDifference_eq_mass τ hτ χ hχ,
    ← (tendsto_corrected_circle_mean_rightGreenMass τ hτ χ hχ).2.limUnder_eq]
  exact exists_hasSum_absolute_exterior_le_circleLimit τ hτ χ hχ φ

open LogQuadrature

/-- Paper: Theorem 12.5.1.1, pp. 519–520.
Reconstruction: the all-width exterior cancellation is equivalent to reaching every
positive upper tolerance cofinally with the finite, pole-corrected ideal measurements. -/
theorem all_widths_iff_cofinal_finiteLogDifference (τ : ℝ≥0ˣ →ₜ* C𝔽)
    (hτ : Function.RightInverse τ (ideleClassNorm F)) :
    allWidths(τ) ↔ ∀ χ : U𝔽, (∀ u : ℝ≥0ˣ, χ (τ u) = 1) →
      ∀ ε : ℝ, 0 < ε → ∀ N : ℕ, ∃ n ≥ N, finiteLogDifference χ n ≤ ε := by
  rw [all_widths_iff_criticalLogDifference_nonpos τ hτ]
  constructor
  · intro h χ hχ ε hε N
    have ht := tendsto_finiteLogDifference_criticalLogDifference τ hτ χ hχ
    obtain ⟨n, hn, hv⟩ := ((eventually_ge_atTop N).and
      (ht.eventually (Iio_mem_nhds ((h χ hχ).trans_lt hε)))).exists
    exact ⟨n, hn, le_of_lt hv⟩
  · intro h χ hχ
    by_contra! hpos
    have ht := tendsto_finiteLogDifference_criticalLogDifference τ hτ χ hχ
    have hv : ∀ᶠ n : ℕ in atTop, criticalLogDifference χ / 2 < finiteLogDifference χ n :=
      ht.eventually (Ioi_mem_nhds (by linarith))
    obtain ⟨N, hN⟩ := eventually_atTop.1 hv
    obtain ⟨n, hn, ha⟩ := h χ hχ (criticalLogDifference χ / 2) (by linarith) N
    exact (hN n hn).not_ge ha

/-- Paper: Theorem 12.5.1.1, pp. 519–520.
Reconstruction: each finite ideal table bounds the full absolute exterior sum with
a quantitative remainder. The two error constants work for every compact test and
every positive width for this normalized character. -/
theorem exists_hasSum_absolute_exterior_le_finiteLogDifference_rate (τ : ℝ≥0ˣ →ₜ* C𝔽)
    (hτ : Function.RightInverse τ (ideleClassNorm F)) (χ : U𝔽)
    (hχ : ∀ u : ℝ≥0ˣ, χ (τ u) = 1) :
    ∃ C > 0, ∃ c > 0, ∀ φ : BruhatCompactSupport C𝔽, ∃ W : ℝ, 0 ≤ W ∧
      ∀ α : ℝ, 0 < α → ∃ A : ℝ,
        HasSum (fun z : {p : ℂ // 0 < ord(χ, p) ∧ α ≤ |p.re-1/2|} ↦
          ‖(ord(χ, z.val) : ℂ) *
            modulatedFourierMellin m𝔽 univ ⟨isProperMap_ideleClassNorm F, ideleClassNorm_ne_one (F := F)⟩
              μ𝔽 φ.val (ideleClassNormTwist χ (z.val - 1/2))‖) A ∧
        ∀ n : ℕ, A ≤ (3*W/(2*α)) *
          (finiteLogDifference χ n + C * Real.exp (-c * Real.sqrt (Real.log n))) := by
  obtain ⟨C, hC, c, hc, hrate⟩ := finiteLogDifference_rate τ hτ χ hχ
  refine ⟨C, hC, c, hc, fun φ ↦ ?_⟩
  obtain ⟨W, hW, h⟩ := exists_hasSum_absolute_exterior_le_criticalLogDifference τ hτ χ hχ φ
  refine ⟨W, hW, fun α hα ↦ ?_⟩
  obtain ⟨A, hA, hbound⟩ := h α hα
  refine ⟨A, hA, fun n ↦ hbound.trans (mul_le_mul_of_nonneg_left ?_ (by positivity))⟩
  linarith [(abs_le.mp (hrate n)).1]

/-- Paper: Theorem 12.5.1.1, pp. 519–520.
For each normalized character and compact test, the absolute exterior sum at each
positive width is bounded by the measured limit. With any positive tolerance, each
sufficiently late finite table gives the same upper bound with that tolerance added. -/
theorem exists_hasSum_absolute_exterior_le_finiteLogDifference (τ : ℝ≥0ˣ →ₜ* C𝔽)
    (hτ : Function.RightInverse τ (ideleClassNorm F)) (χ : U𝔽)
    (hχ : ∀ u : ℝ≥0ˣ, χ (τ u) = 1) (φ : BruhatCompactSupport C𝔽) :
    ∃ W : ℝ, 0 ≤ W ∧ ∀ α : ℝ, 0 < α → ∃ A : ℝ,
      HasSum (fun z : {p : ℂ // 0 < ord(χ, p) ∧ α ≤ |p.re-1/2|} ↦
        ‖(ord(χ, z.val) : ℂ) *
          modulatedFourierMellin m𝔽 univ ⟨isProperMap_ideleClassNorm F, ideleClassNorm_ne_one (F := F)⟩
            μ𝔽 φ.val (ideleClassNormTwist χ (z.val - 1/2))‖) A ∧
      A ≤ (3*W/(2*α)) * limUnder atTop (finiteLogDifference χ) ∧
      ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop, A ≤ (3*W/(2*α)) * (finiteLogDifference χ n + ε) := by
  obtain ⟨W, hW, h⟩ := exists_hasSum_absolute_exterior_le_criticalLogDifference τ hτ χ hχ φ
  have ht := tendsto_finiteLogDifference_criticalLogDifference τ hτ χ hχ
  refine ⟨W, hW, fun α hα ↦ ?_⟩
  obtain ⟨A, hA, hb⟩ := h α hα
  refine ⟨A, hA, ht.limUnder_eq.symm ▸ hb, fun ε hε ↦ ?_⟩
  have hl : ∀ᶠ n : ℕ in atTop, criticalLogDifference χ - ε < finiteLogDifference χ n :=
    ht.eventually (Ioi_mem_nhds (by linarith))
  filter_upwards [hl] with n hn
  exact hb.trans (mul_le_mul_of_nonneg_left (by linarith) (by positivity))

end CompactGreen

end RiemannMasullo.Isolated
