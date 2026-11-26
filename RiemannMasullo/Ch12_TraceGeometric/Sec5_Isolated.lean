module

public import RiemannMasullo.ForMathlib.Analysis.Fourier.PositiveLaplaceEdges
public import RiemannMasullo.Ch12_TraceGeometric.Sec4_UpperFrequencyGate
public import RiemannMasullo.AppA_AlgebraicNT.Sec5a_IdeleClassDPrime
import RiemannMasullo.Ch01_Introduction.Sec4
import RiemannMasullo.AppB_AnalyticNT.Sec4b
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Geometry.Manifold.PartitionOfUnity
import RiemannMasullo.Ch10_TraceSpectral.Sec3_LineQuotientWindows
public import RiemannMasullo.Ch12_TraceGeometric.Sec5

/-! # Isolated statements of §12.5

Statements of the section that are neither proved nor refuted and that nothing else in Lean
uses, with what follows from them (`AGENTS.md`, "False statements and gaps"). Nothing imports
this file.

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

namespace RiemannMasullo.Isolated.OutputOrderGeometry

open Complex Filter Function IsDedekindDomain
open scoped NumberField.AdeleRing Topology ContDiff

set_option quotPrecheck false
attribute [local instance] instIdeleClassMeasurableSpaceSec1 instIdeleClassBorelSpaceSec1
  instIdeleClassT2Sec1 instIdeleClassLocallyCompactSec1 instIdeleClassSecondCountableSec1
  instIdeleClassHaarMeasureSec1 instFiniteCompletionUnitsLocallyCompactSec4b
variable {F : Type*} [Field F] [NumberField F]
local notation "C𝔽" => IdeleClassGroup (𝓞 F) F
local notation "μ𝔽" => ideleClassTamagawaMeasure F
local notation "m𝔽" => (continuousIdeleClassNorm F : C𝔽 →ₜ* ℝ≥0ˣ)
local notation "ord(" χ ", " z ")" => MeromorphicOn.divisor (continuedCompletedHeckeL (F := F) χ) univ z
local notation "Sites(" χ ")" => {z : ℂ // 0 < ord(χ,z)}
local notation "M(" φ ", " χ ", " z ")" => modulatedFourierMellin m𝔽 univ
  ⟨isProperMap_ideleClassNorm F, ideleClassNorm_ne_one (F := F)⟩ μ𝔽 (φ : BruhatCompactSupport C𝔽).val
  (ideleClassNormTwist (F := F) χ ((z : ℂ) - 1/2))

local notation "C₁" => (ideleClassNorm F).ker
local notation "Chars(" τ ")" => {χ : PontryaginDual C𝔽 // ∀ t : ℝ≥0ˣ, χ (τ t) = 1}
local notation "outside(" τ ", " χ ", " φ ")" => (∀ η : PontryaginDual C𝔽,
  (∀ t, η (τ t) = 1) → η ≠ (χ).val → ∀ z : ℂ, M(φ,η,z) = 0)
local notation "Vf" => HeightOneSpectrum (𝓞 F)
local notation "volC" => (((normOneIdeleClassTamagawaMeasure F) univ).toReal : ℂ)
local notation "archClass(" w ")" => IdeleClassGroup.ofCompletion (𝓞 F) F w
local notation "finiteClass(" v ")" => IdeleClassGroup.ofAdicCompletion (𝓞 F) F v
local notation "finiteV(" v ")" => (finiteLocalMultiplicativeTamagawaMeasure F v
  ((HeightOneSpectrum.adicCompletionIntegers F v).units : Set _)).toReal
local notation "finTerm(" v ", " b ")" => ((Real.log ((v : Vf).asIdeal.absNorm : ℝ) / finiteV(v) : ℝ) : ℂ) *
  finiteConnesWeilPrincipalValue v 1 b
local notation "rawM(" φ ", " χ ", " w ")" => modulatedFourierMellin m𝔽 univ
  ⟨isProperMap_ideleClassNorm F, ideleClassNorm_ne_one (F := F)⟩ μ𝔽 (φ : BruhatCompactSupport C𝔽).val
  (ideleClassNormTwist (F := F) χ w)
local notation "localSum(" φ ", " A ", " B ")" =>
  rawM(φ,(1 : PontryaginDual C𝔽),(1/2)) + rawM(φ,(1 : PontryaginDual C𝔽),(-1/2)) -
    volC * ((∑ w : InfinitePlace F, infiniteConnesWeilPrincipalValue w (A w)) +
      ∑' v : Vf, finTerm(v,B v))

local notation "ext(" τ ", " α ")" => {p : Chars(τ) × ℂ //
  0 < ord(p.1.val,p.2) ∧ α ≤ |p.2.re-1/2|}
local notation "target(" τ ")" => (∀ (α : ℝ), 0 < α → ∀ f : BruhatCompactSupport C𝔽,
  (∀ g : C₁, f.val g = 0) → HasSum (fun p : ext(τ,α) ↦
    ((ord(p.val.1.val,p.val.2) : ℤ) : ℂ)*M(f,p.val.1.val,p.val.2)) 0)

private theorem normOneVolume_pos : 0 < ((normOneIdeleClassTamagawaMeasure F) univ).toReal := by
  rw [normOneIdeleClassTamagawaMeasure_volume]
  have := NumberField.Units.regulator_pos F
  have := NumberField.classNumber_pos F
  have := NumberField.Units.torsionOrder_pos F
  have : (0 : ℝ) < Real.sqrt (Int.natAbs (NumberField.discr F) : ℝ) :=
    Real.sqrt_pos.mpr (by exact_mod_cast Int.natAbs_pos.mpr (NumberField.discr_ne_zero F))
  exact ENNReal.toReal_pos (ENNReal.ofReal_pos.mpr (by positivity)).ne' ENNReal.ofReal_ne_top

private theorem logNormMellin (H : ℝ → ℂ) (s : ℂ) :
    introTraceMellin (fun r ↦ H (Real.log r)) s = bilateralLaplace H s := by
  rw [introTraceMellin,mellin,← integral_comp_exp,bilateralLaplace]
  apply integral_congr_ae
  filter_upwards with x
  simp only [Real.log_exp,Complex.real_smul,smul_eq_mul]
  rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast (Real.exp_pos x).ne'),
    ← Complex.ofReal_log (Real.exp_pos x).le, Real.log_exp, Complex.ofReal_exp,
    ← mul_assoc, ← Complex.exp_add,mul_comm]
  congr 1
  ring_nf

private theorem normalized_otherMoment_eq_zero (τ : ℝ≥0ˣ →ₜ* C𝔽)
    (hτ : RightInverse τ (ideleClassNorm F)) (χ η : PontryaginDual C𝔽)
    (hχ : ∀ t, χ (τ t) = 1) (hη : ∀ t, η (τ t) = 1) (hne : η ≠ χ)
    (f : ℝ → ℂ) (φ : BruhatCompactSupport C𝔽) (hφ : ∀ g, φ.val g = introTraceTest χ f g)
    (z : ℂ) : M(φ,η,z) = 0 := by
  obtain ⟨y, hy⟩ : ∃ y, η y ≠ χ y := not_forall.mp (fun h ↦ hne (DFunLike.ext _ _ h))
  let u : (ideleClassNorm F).ker := ⟨y * (τ (ideleClassNorm F y))⁻¹, by
    change ideleClassNorm F _ = 1
    rw [map_mul, map_inv, hτ, mul_inv_cancel]⟩
  have huχ : χ u.val = χ y := by simp [u, hχ]
  have huη : η u.val = η y := by simp [u, hη]
  let d : ℂ := star (χ u.val : ℂ) * (η u.val : ℂ)
  have hd : d ≠ 1 := by
    intro hd
    have hunit : (χ u.val : ℂ) * star (χ u.val : ℂ) = 1 := by
      simp [← Circle.coe_inv_eq_conj]
    have he : (η u.val : ℂ) = (χ u.val : ℂ) := by
      dsimp only [d] at hd
      linear_combination (χ u.val : ℂ) * hd - (η u.val : ℂ) * hunit
    exact hy (Subtype.ext (by simpa only [huχ, huη] using he))
  let W (g : C𝔽) := φ.val g * ideleClassNormTwist η (z-1/2) g
  have hW (x : C𝔽) : W (u.val * x) = d * W x := by
    rw [mul_comm u.val x]
    have ht : ideleClassNormTwist η (z-1/2) u.val = (η u.val : ℂ) := by
      change (η u.val : ℂ) * (((ideleClassNorm F u.val).val : ℝ) : ℂ) ^ (z-1/2) = _
      simp [show ideleClassNorm F u.val = 1 from u.property]
    simp only [W, d, map_mul, ht, hφ, introTraceTest_mul_normOne]
    ring
  let m := ideleClassTamagawaMeasure F
  have hi : (∫ g, W g ∂m) = d * ∫ g, W g ∂m := by
    calc
      _ = ∫ g, W (u.val * g) ∂m := (integral_mul_left_eq_self (μ := m) W u.val).symm
      _ = _ := by rw [← integral_const_mul]; exact integral_congr_ae (.of_forall hW)
  have hzero : (∫ g, W g ∂m) = 0 :=
    (mul_eq_zero.mp (show (1-d) * (∫ g, W g ∂m) = 0 by linear_combination hi)).resolve_left
      (fun he ↦ hd (sub_eq_zero.mp he).symm)
  simpa only [modulatedFourierMellin, relativeVerticalStrip, Set.preimage_univ, Set.indicator_univ]
    using hzero

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

/-- A smooth even profile inside the first prime shell, chosen before the number field. -/
def primeFreeProfile : ℝ → ℝ :=
  (exists_smallSupport_polarFree_positiveLaplace (B := 1/2) (R := Real.log 2)
    (by norm_num) (Real.log_pos (by norm_num))).choose

theorem primeFreeProfile_properties :
    ContDiff ℝ (∞) primeFreeProfile ∧ HasCompactSupport primeFreeProfile ∧
    tsupport primeFreeProfile ⊆ Ioo (-Real.log 2) (Real.log 2) ∧
    (∀ x, primeFreeProfile (-x) = primeFreeProfile x) ∧ 0 < primeFreeProfile 0 ∧
    bilateralLaplace (fun x ↦ (primeFreeProfile x : ℂ)) (1/2) = 0 ∧
    bilateralLaplace (fun x ↦ (primeFreeProfile x : ℂ)) (-(1/2)) = 0 ∧
    ∀ w : ℂ, |w.re| < 1/2 → 0 < (bilateralLaplace (fun x ↦ (primeFreeProfile x : ℂ)) w).re := by
  simpa only [primeFreeProfile,Complex.ofReal_div,Complex.ofReal_one,Complex.ofReal_ofNat] using
    (exists_smallSupport_polarFree_positiveLaplace (B := 1/2) (R := Real.log 2)
      (by norm_num) (Real.log_pos (by norm_num))).choose_spec

/-- The rational local min-power correction of the chosen short profile is strictly positive. -/
theorem primeFreeProfile_minPower_pos :
    0 < ∫ x : ℝ, Real.exp (-(1/2 : ℝ) * |x|) * primeFreeProfile x := by
  obtain ⟨hs,hc,_,_,_,_,_,hstrip⟩ := primeFreeProfile_properties
  apply integral_exp_neg_abs_mul_pos_of_bilateralLaplace primeFreeProfile hc hs _ (by norm_num)
  intro t
  apply hstrip
  simp

section UpperFrequencyGates

open RationalUpperGate

/-- The centered test of §12.5 gives a positive lower bound for the compensated
rank-one defect of every normalized rational upper frequency gate at fixed spatial scale. -/
theorem primeFreeProfile_upperGate {Q : ℝ → ℝ} (hQ : Measurable Q)
    (hbound : ∀ u ∈ Ioc (0 : ℝ) 1, Q u ∈ Icc 0 1)
    (hplateau : ∃ δ > 0, ∀ u ∈ Ioc 0 δ, Q u = 1) :
    0 < rankOneDefect primeFreeProfile (fun _ ↦ 1) ∧
    rankOneDefect primeFreeProfile (fun _ ↦ 1) +
      (1 - 1 / Real.sqrt 2) * primeFreeProfile 0 * logLoss Q ≤
      rankOneDefect primeFreeProfile Q + primeFreeProfile 0 * logLoss Q ∧
    0 < rankOneDefect primeFreeProfile Q + primeFreeProfile 0 * logLoss Q := by
  obtain ⟨hs, _, hS, heven, _, _, _, hstrip⟩ := primeFreeProfile_properties
  apply compensated_defect_of_positive_spectrum hs hS heven _ hQ hbound hplateau
  intro t
  apply hstrip
  simp

private theorem primeFreeProfile_negHalfMoment :
    (∫ x : ℝ, primeFreeProfile x * Real.exp (-x / 2)) = 0 := by
  obtain ⟨_, _, _, _, _, _, hpolar, _⟩ := primeFreeProfile_properties
  rw [halfMoment_eq_re_bilateralLaplace]
  simpa only [neg_div, Complex.zero_re] using congrArg Complex.re hpolar

/-- A forward translate by at least `log 2` kills the actual short test's rank-one
gate term for every gate and its physical value at norm one. -/
theorem primeFreeProfile_translated_upperGate (Q : ℝ → ℝ) {y : ℝ} (hy : Real.log 2 ≤ y) :
    rankOneDefect (fun x ↦ primeFreeProfile (x - y)) Q = 0 ∧ primeFreeProfile (-y) = 0 := by
  obtain ⟨_, _, hS, _⟩ := primeFreeProfile_properties
  simpa only [primeFreeProfile_negHalfMoment, mul_zero] using
    rankOneDefect_translate_of_le Q hS hy

/-- At the half-width frequency gate and reciprocal spatial scale two, the chosen
test has zero rank-one term and its total local scale correction is zero. -/
theorem primeFreeProfile_balancedHalfGate :
    rankOneDefect primeFreeProfile (upperStep (1/2)) = 0 ∧
    logLoss (upperStep (1/2)) = Real.log 2 ∧
    ∀ P : ℂ, P + ((primeFreeProfile 0 * (Real.log 2 - logLoss (upperStep (1/2))) -
      rankOneDefect primeFreeProfile (upperStep (1/2)) : ℝ) : ℂ) = P := by
  obtain ⟨_, _, hS, _, _, _, hpolar, _⟩ := primeFreeProfile_properties
  obtain ⟨hD, hL⟩ := upperStep_half_of_polar (fun x hx ↦ (hS hx).1.le) hpolar
  refine ⟨hD, hL, fun P ↦ ?_⟩
  rw [hD, hL, sub_self, mul_zero, sub_zero, Complex.ofReal_zero, add_zero]

end UpperFrequencyGates

private theorem primeFreeProfile_complex_smooth :
    ContDiff ℝ (∞) (fun x ↦ (primeFreeProfile x : ℂ)) :=
  Complex.ofRealCLM.contDiff.comp primeFreeProfile_properties.1

private theorem primeFreeProfile_complex_compact :
    HasCompactSupport (fun x ↦ (primeFreeProfile x : ℂ)) :=
  primeFreeProfile_properties.2.1.comp_left Complex.ofReal_zero

/-- The compact idèle-class test has the inverse of the character indexing its zeros. -/
def primeFreeCharacterTest (χ : PontryaginDual C𝔽) : BruhatCompactSupport C𝔽 :=
  (exists_characterNormTest (F := F) χ⁻¹ (fun x ↦ (primeFreeProfile x : ℂ))
    (Complex.ofRealCLM.contDiff.comp primeFreeProfile_properties.1)
    (primeFreeProfile_properties.2.1.comp_left Complex.ofReal_zero)).choose

theorem primeFreeCharacterTest_apply (χ : PontryaginDual C𝔽) (g : C𝔽) :
    (primeFreeCharacterTest χ).val g =
      (χ⁻¹ g : ℂ) * (primeFreeProfile (logIdeleClassNorm F g) : ℂ) :=
  (exists_characterNormTest (F := F) χ⁻¹ _ primeFreeProfile_complex_smooth
    primeFreeProfile_complex_compact).choose_spec g

/-- At the identity, the angular factor disappears and the short profile is positive. -/
theorem primeFreeCharacterTest_apply_one (χ : PontryaginDual C𝔽) :
    (primeFreeCharacterTest χ).val 1 = (primeFreeProfile 0 : ℂ) := by
  simpa [logIdeleClassNorm] using primeFreeCharacterTest_apply χ 1

local notation "φχ(" χ ")" => primeFreeCharacterTest (F := F) χ
local notation "Aχ(" χ ", " w ")" => (idelicExplicitFormula_infiniteTestMap (F := F) w).choose φχ(χ)
local notation "Bχ(" χ ", " v ")" => (idelicExplicitFormula_finiteTestMap (F := F) v).choose φχ(χ)
local notation "Wχ(" χ ", " z ")" => (((ord(χ,(z : ℂ))).toNat : ℝ) * (M(φχ(χ),χ,(z : ℂ))).re)

/-- The local tests in the comparison are the restrictions of the same global
test along the canonical embeddings at every infinite and finite place. -/
theorem primeFreeCharacterTest_localRestrictions (χ : PontryaginDual C𝔽) :
    (∀ (w : InfinitePlace F) (u : w.Completionˣ), (Aχ(χ,w)).val u = (φχ(χ)).val (archClass(w) u)) ∧
    (∀ (v : Vf) (u : (v.adicCompletion F)ˣ), (Bχ(χ,v)).val u = (φχ(χ)).val (finiteClass(v) u)) :=
  ⟨fun w ↦ (idelicExplicitFormula_infiniteTestMap (F := F) w).choose_spec _,
    fun v ↦ (idelicExplicitFormula_finiteTestMap (F := F) v).choose_spec _⟩

/-- The geometric scalar from the actual archimedean principal values and the
logarithm of the product of the discriminant and the conductor. -/
def primeFreeArchConductor (χ : PontryaginDual C𝔽) : ℝ :=
  ((normOneIdeleClassTamagawaMeasure F) univ).toReal *
    ((∑ w : InfinitePlace F, infiniteConnesWeilPrincipalValue w Aχ(χ,w)).re -
      primeFreeProfile 0 * heckeLogDiscriminantConductor χ)

/-- The single-character numerical identity supplied by the Weil explicit formula
at this prescribed compact test. Compare A. Connes, *Trace formula in noncommutative
geometry and the zeros of the Riemann zeta function*, Appendix II, Theorem 6,
pp. 77–78, applied to `|g|⁻¹ᐟ² φ(g⁻¹)`. With the Tamagawa measures of §12.5
the local principal values are multiplied by the volume of the norm-one group. -/
def PrimeFreeWeilIdentity (χ : PontryaginDual C𝔽) : Prop :=
  (∑' z : Sites(χ), Wχ(χ,z)) =
    (localSum(φχ(χ),(fun w ↦ Aχ(χ,w)),(fun v ↦ Bχ(χ,v)))).re

private theorem characterTest_introTrace (χ : PontryaginDual C𝔽) (g : C𝔽) :
    (φχ(χ)).val g = introTraceTest χ (fun r ↦ (primeFreeProfile (Real.log r) : ℂ)) g := by
  rw [primeFreeCharacterTest_apply, introTraceTest, show χ⁻¹ g = (χ g)⁻¹ from rfl,
    Circle.coe_inv_eq_conj]
  rfl

theorem primeFreeCharacterTest_mellin (χ : PontryaginDual C𝔽) (z : ℂ) :
    M(φχ(χ),χ,z) = volC * bilateralLaplace (fun x ↦ (primeFreeProfile x : ℂ)) (z - 1/2) := by
  have h := (introTraceTest_mellin χ _ (φχ(χ)) (characterTest_introTrace χ) (z-1/2)).2
  rw [← logNormMellin (fun x ↦ (primeFreeProfile x : ℂ))]
  simpa only [modulatedFourierMellin, relativeVerticalStrip, Set.preimage_univ,
    Set.indicator_univ] using h

private theorem primeFreeCharacterTest_outside (τ : ℝ≥0ˣ →ₜ* C𝔽)
    (hτ : RightInverse τ (ideleClassNorm F)) (χ : Chars(τ)) : outside(τ,χ,φχ(χ.val)) :=
  fun η hη hne z ↦ normalized_otherMoment_eq_zero τ hτ χ.val η χ.property hη hne _
    (φχ(χ.val)) (characterTest_introTrace χ.val) z

/-- Both principal polar moments of the fixed test vanish for every normalized character. -/
theorem primeFreeCharacterTest_polar (τ : ℝ≥0ˣ →ₜ* C𝔽)
    (hτ : RightInverse τ (ideleClassNorm F)) (χ : Chars(τ)) :
    rawM(φχ(χ.val),(1 : PontryaginDual C𝔽),(-1/2)) = 0 ∧
    rawM(φχ(χ.val),(1 : PontryaginDual C𝔽),(1/2)) = 0 := by
  have hpol : M(φχ(χ.val),(1 : PontryaginDual C𝔽),(0:ℂ)) = 0 ∧
      M(φχ(χ.val),(1 : PontryaginDual C𝔽),(1:ℂ)) = 0 := by
    by_cases h : (1 : PontryaginDual C𝔽) = χ.val
    · rw [h,primeFreeCharacterTest_mellin,primeFreeCharacterTest_mellin,zero_sub,
        show (1:ℂ)-1/2 = 1/2 by ring]
      obtain ⟨_,_,_,_,_,hp,hm,_⟩ := primeFreeProfile_properties
      simp only [hp, hm, mul_zero, and_self]
    · have hoff := primeFreeCharacterTest_outside τ hτ χ
      exact ⟨hoff 1 (by simp) h 0,hoff 1 (by simp) h 1⟩
  exact ⟨by simpa only [zero_sub,neg_div] using hpol.1,
    by simpa only [show (1:ℂ)-1/2 = 1/2 by ring] using hpol.2⟩

theorem primeFreeCharacterTest_mellin_pos (τ : ℝ≥0ˣ →ₜ* C𝔽)
    (hτ : RightInverse τ (ideleClassNorm F)) (χ : Chars(τ)) (z : Sites(χ.val)) :
    0 < (M(φχ(χ.val),χ.val,z.val)).re := by
  rw [primeFreeCharacterTest_mellin, Complex.re_ofReal_mul]
  apply mul_pos (normOneVolume_pos (F := F))
  obtain ⟨_,_,_,_,_,_,_,hstrip⟩ := primeFreeProfile_properties
  apply hstrip
  have hempty := (hasSum_exteriorZeros_iff_isEmpty τ hτ (1/2)).mp
    (fun φ _ ↦ traceFormula_exteriorZeros_of_half_le τ φ le_rfl)
  have hsite : |z.val.re - 1/2| < 1/2 :=
    lt_of_not_ge fun h ↦ hempty.false ⟨(χ,z.val),z.property,h⟩
  simpa using hsite

/-- The actual finite restrictions of this test have finite support in the Weil
sum and their normalized sum is its negative conductor contribution. -/
theorem primeFreeCharacterTest_finitePrincipalValues (χ : PontryaginDual C𝔽) :
    (Function.support (fun v : Vf ↦ finTerm(v,Bχ(χ,v)))).Finite ∧
    HasSum (fun v : Vf ↦ finTerm(v,Bχ(χ,v)))
      (-(primeFreeProfile 0 : ℂ) * (heckeLogDiscriminantConductor χ : ℂ)) := by
  have hs : tsupport (fun x ↦ (primeFreeProfile x : ℂ)) ⊆ Ioo (-Real.log 2) (Real.log 2) :=
    (tsupport_comp_subset (g := ((↑) : ℝ → ℂ)) Complex.ofReal_zero primeFreeProfile).trans
      primeFreeProfile_properties.2.2.1
  exact hasSum_finitePrincipalValues_characterLogProfile χ _ hs (φχ(χ))
    (primeFreeCharacterTest_apply χ) _ (fun v ↦ (idelicExplicitFormula_finiteTestMap (F := F) v).choose_spec _)

/-- Assuming the single-character Weil identity identifies its sum, the genuine
positive zero masses sum to the negative of the geometric scalar in §12.5. -/
theorem hasSum_primeFreeArchConductor_of_weil (τ : ℝ≥0ˣ →ₜ* C𝔽)
    (hτ : RightInverse τ (ideleClassNorm F)) (χ : Chars(τ)) (hWeil : PrimeFreeWeilIdentity χ.val) :
    HasSum (fun z : Sites(χ.val) ↦ Wχ(χ.val,z)) (-primeFreeArchConductor χ.val) := by
  have hpos := primeFreeCharacterTest_mellin_pos τ hτ χ
  have hs := (ConditionalOutputOrder.summable_fullRealMoments χ.val (φχ(χ.val))).congr
    (fun z ↦ by rw [abs_of_pos (hpos z)])
  have hpol := primeFreeCharacterTest_polar τ hτ χ
  have hfin := (primeFreeCharacterTest_finitePrincipalValues χ.val).2.tsum_eq
  unfold PrimeFreeWeilIdentity at hWeil
  rw [hpol.1, hpol.2, hfin, zero_add, zero_sub, Complex.neg_re,
    Complex.re_ofReal_mul, Complex.add_re] at hWeil
  simp only [neg_mul, Complex.neg_re, ← Complex.ofReal_mul, Complex.ofReal_re, ← sub_eq_add_neg] at hWeil
  exact hWeil ▸ hs.hasSum

private theorem summable_masked_weight {ι : Type*} (P : ι → Prop) [DecidablePred P]
    (n q : ι → ℕ) (v : ι → ℝ) (h : Summable (fun i ↦ (n i : ℝ) * |v i|))
    (hq : ∀ i, q i ≤ n i) :
    Summable (fun i ↦ if P i then (q i : ℝ) * v i else 0) := by
  apply h.of_norm_bounded
  intro i
  by_cases hp : P i
  · simp only [hp, ite_true, Real.norm_eq_abs, abs_mul, Nat.abs_cast]
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast hq i) (abs_nonneg (v i))
  · simp only [hp, ite_false, norm_zero]
    exact mul_nonneg (Nat.cast_nonneg (n i)) (abs_nonneg (v i))

private theorem full_split {ι : Type*} (P : ι → Prop) [DecidablePred P]
    (n : ι → ℕ) (v : ι → ℝ) (h : Summable (fun i ↦ (n i : ℝ) * |v i|)) :
    (∑' i, (n i : ℝ) * v i) = (∑' i, if P i then (n i : ℝ) * v i else 0) +
      ∑' i, if ¬ P i then (n i : ℝ) * v i else 0 := by
  have hc := summable_masked_weight P n n v h (fun _ ↦ le_rfl)
  have he := summable_masked_weight (fun i ↦ ¬ P i) n n v h (fun _ ↦ le_rfl)
  rw [← hc.tsum_add he]
  apply tsum_congr
  intro i
  by_cases hp : P i <;> simp only [hp, not_true_eq_false, not_false_eq_true,
    ite_true, ite_false, add_zero, zero_add]

private theorem split_at_order {ι : Type*} (P : ι → Prop) [DecidablePred P]
    (n : ι → ℕ) (v : ι → ℝ) (h : Summable (fun i ↦ (n i : ℝ) * |v i|)) (k : ℕ) :
    (∑' i, (n i : ℝ) * v i) -
      (∑' i, if P i then ((min (n i) (k+1) : ℕ) : ℝ) * v i else 0) =
      (∑' i, if ¬ P i then (n i : ℝ) * v i else 0) +
      ∑' i, if P i then (((n i)-(k+1) : ℕ) : ℝ) * v i else 0 := by
  let cap (i : ι) := if P i then ((min (n i) (k+1) : ℕ) : ℝ) * v i else 0
  let rem (i : ι) := if P i then (((n i)-(k+1) : ℕ) : ℝ) * v i else 0
  have hc : Summable cap := summable_masked_weight P n _ v h (fun i ↦ min_le_left _ _)
  have hr : Summable rem := summable_masked_weight P n _ v h (fun i ↦ Nat.sub_le _ _)
  have hcentral : (∑' i, if P i then (n i : ℝ) * v i else 0) = (∑' i, cap i) + ∑' i, rem i := by
    rw [← hc.tsum_add hr]
    apply tsum_congr
    intro i
    by_cases hp : P i
    · have hnat : n i = min (n i) (k+1) + (n i - (k+1)) := by omega
      have hreal : (n i : ℝ) = ((min (n i) (k+1) : ℕ) : ℝ) + ((n i - (k+1) : ℕ) : ℝ) := by
        exact_mod_cast hnat
      simp only [cap, rem, hp, ite_true]
      exact (congrArg (· * v i) hreal).trans (add_mul _ _ _)
    · simp only [cap, rem, hp, ite_false, add_zero]
  change _ - (∑' i, cap i) = _ + ∑' i, rem i
  rw [full_split P n v h, hcentral]
  ring

private theorem exterior_zero_iff {ι : Type*} (P : ι → Prop) [DecidablePred P]
    (n : ι → ℕ) (v : ι → ℝ) (h : Summable (fun i ↦ (n i : ℝ) * |v i|))
    (hn : ∀ i, 0 < n i) (hv : ∀ i, 0 < v i) :
    (∑' i, if ¬ P i then (n i : ℝ) * v i else 0) = 0 ↔ ∀ i, P i := by
  have he := summable_masked_weight (fun i ↦ ¬ P i) n n v h (fun _ ↦ le_rfl)
  have hnon (i : ι) : 0 ≤ (if ¬ P i then (n i : ℝ) * v i else 0) :=
    ite_nonneg (mul_nonneg (Nat.cast_nonneg _) (hv i).le) le_rfl
  constructor
  · intro hz i
    by_contra hi
    have hpos : 0 < (if ¬ P i then (n i : ℝ) * v i else 0) := by
      rw [ite_eq_left hi]
      exact mul_pos (by exact_mod_cast hn i) (hv i)
    exact (he.tsum_pos hnon i hpos).ne' hz
  · intro hp
    simp only [hp, not_true_eq_false, ite_false, tsum_zero]

private theorem approximates_iff_limUnder_le (I : ℕ → ℝ) (L V : ℝ)
    (ht : Tendsto I atTop (𝓝 L)) (hb : ∀ k, L ≤ I k) :
    (∀ δ : ℝ, 0 < δ → ∃ k, I k ≤ -V + δ) ↔ limUnder atTop I ≤ -V := by
  rw [ht.limUnder_eq]
  constructor
  · intro h
    by_contra! hlarge
    obtain ⟨k,hk⟩ := h ((L+V)/2) (by linarith)
    linarith [hb k]
  · intro h δ hδ
    have he : ∀ᶠ k in atTop, I k < -V + δ :=
      ht.eventually (eventually_lt_nhds (by linarith : L < -V + δ))
    exact he.exists.imp fun k hk ↦ hk.le
private theorem centralComparison_of_capped (ι : Type*) (P : ι → Prop) [DecidablePred P]
    (n : ι → ℕ) (v : ι → ℝ) (hn : ∀ i, 0 < n i) (hv : ∀ i, 0 < v i)
    (hs : Summable (fun i ↦ (n i : ℝ) * |v i|)) (J : ℕ → ℝ) (T : ℝ)
    (hT : -T = ∑' i, (n i : ℝ) * v i)
    (hJ : ∀ k : ℕ, J k = -(∑' i, if P i then ((min (n i) (k+1) : ℕ) : ℝ)*v i else 0))
    (hlim : Tendsto J atTop (𝓝 (-(∑' i, if P i then (n i : ℝ)*v i else 0)))) :
    (∀ k : ℕ, J k - T = (∑' i, if ¬ P i then (n i : ℝ)*v i else 0) +
      ∑' i, if P i then ((n i - (k+1) : ℕ) : ℝ)*v i else 0) ∧
    Tendsto (fun k ↦ J k - T) atTop (𝓝 (∑' i, if ¬ P i then (n i : ℝ)*v i else 0)) ∧
    ((∀ δ : ℝ, 0 < δ → ∃ k : ℕ, J k ≤ T + δ) ↔ ∀ i, P i) ∧
    ((limUnder atTop J ≤ T) ↔ ∀ i, P i) := by
  let L := -(∑' i, if P i then (n i : ℝ)*v i else 0)
  let E := ∑' i, if ¬ P i then (n i : ℝ)*v i else 0
  change Tendsto J atTop (𝓝 L) at hlim
  have he : L - T = E := by
    dsimp only [L, E]
    rw [sub_eq_add_neg, hT, full_split P n v hs]
    ring
  have hE : 0 ≤ E := tsum_nonneg fun i ↦ ite_nonneg (mul_nonneg (Nat.cast_nonneg _) (hv i).le) le_rfl
  have hlow (k : ℕ) : L ≤ J k := by
    rw [hJ]
    apply neg_le_neg
    apply (summable_masked_weight P n _ v hs (fun i ↦ min_le_left _ _)).tsum_le_tsum _
      (summable_masked_weight P n n v hs (fun _ ↦ le_rfl))
    intro i
    by_cases hp : P i
    · simp only [hp, ite_true]
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast min_le_left (n i) (k+1)) (hv i).le
    · simp [hp]
  have hzero := exterior_zero_iff P n v hs hn hv
  have hequiv : (limUnder atTop J ≤ T) ↔ ∀ i, P i := by
    rw [hlim.limUnder_eq]
    have heq : L ≤ T ↔ E = 0 := by constructor <;> intro h <;> linarith
    exact heq.trans hzero
  refine ⟨?_, ?_, ?_, hequiv⟩
  · intro k
    rw [hJ, sub_eq_add_neg, hT, add_comm, ← sub_eq_add_neg]
    exact split_at_order P n v hs k
  · change Tendsto (fun k ↦ J k - T) atTop (𝓝 E)
    rw [← he]
    exact hlim.sub_const T
  · refine Iff.trans ?_ hequiv
    simpa only [neg_neg] using approximates_iff_limUnder_le J L (-T) hlim hlow

local notation "centered(" z ")" => ((z : ℂ).re = 1/2)
local notation "ordN(" χ ", " z ")" => (ord(χ,(z : ℂ))).toNat
local notation "valueχ(" χ ", " z ")" => (M(φχ(χ),χ,(z : ℂ))).re
local notation "exteriorMass(" χ ")" => (∑' z : Sites(χ), if ¬ centered(z.val) then Wχ(χ,z) else 0)
local notation "remainingOrder(" χ ", " k ")" => (∑' z : Sites(χ), if centered(z.val) then
  ((ordN(χ,z.val) - (k+1) : ℕ) : ℝ) * valueχ(χ,z.val) else 0)

private theorem primeFree_cappedComparison (τ : ℝ≥0ˣ →ₜ* C𝔽)
    (hτ : RightInverse τ (ideleClassNorm F)) (χ : Chars(τ))
    (hWeil : PrimeFreeWeilIdentity χ.val) (J : ℕ → ℝ)
    (hJ : ∀ k : ℕ, J k = -(∑' z : Sites(χ.val), if centered(z.val) then
      ((min (ordN(χ.val,z.val)) (k+1) : ℕ) : ℝ) * valueχ(χ.val,z.val) else 0))
    (hlim : Tendsto J atTop (𝓝 (-(∑' z : Sites(χ.val), if centered(z.val) then Wχ(χ.val,z) else 0)))) :
    (∀ k : ℕ, J k - primeFreeArchConductor χ.val =
      exteriorMass(χ.val) + remainingOrder(χ.val,k)) ∧
    Tendsto (fun k ↦ J k - primeFreeArchConductor χ.val) atTop (𝓝 (exteriorMass(χ.val))) ∧
    ((∀ δ : ℝ, 0 < δ → ∃ k : ℕ, J k ≤ primeFreeArchConductor χ.val + δ) ↔
      ∀ z : Sites(χ.val), centered(z.val)) ∧
    ((limUnder atTop J ≤ primeFreeArchConductor χ.val) ↔ ∀ z : Sites(χ.val), centered(z.val)) := by
  classical
  apply centralComparison_of_capped (Sites(χ.val)) (fun z ↦ centered(z.val))
    (fun z ↦ ordN(χ.val,z.val)) (fun z ↦ valueχ(χ.val,z.val))
  · intro z
    have hz := z.property
    omega
  · exact primeFreeCharacterTest_mellin_pos τ hτ χ
  · exact ConditionalOutputOrder.summable_fullRealMoments χ.val (φχ(χ.val))
  · exact (hasSum_primeFreeArchConductor_of_weil τ hτ χ hWeil).tsum_eq.symm
  · exact hJ
  · exact hlim


/-- The real centered Haar integral at order `k`, evaluated on the prescribed
inverse-character test. The subtraction of its value at the identity is inside
the Haar integral. -/
def primeFreeCenteredIntegral (χ : PontryaginDual C𝔽) (k : ℕ)
    (hQ : ConditionalOutputOrder.QuotientNuclear (φχ(χ)) k) (U : ℕ → Set C𝔽) : ℝ :=
  (∫ x, ConditionalOutputOrder.lineOrderDiagonal k (φχ(χ)) hQ U x - (φχ(χ)).val 1 ∂μ𝔽).re

/-- Paper: Theorem 12.5.1.1, pp. 519–520. With the single-test Weil identity and
quotient nuclearity at each chosen order, the excess over the signed local
scalar is the off-line zero mass plus the unresolved central multiplicities.
Letting the order grow gives the off-line mass and the two upper comparisons. -/
theorem primeFree_centeredComparison_of_weil_nuclear (τ : ℝ≥0ˣ →ₜ* C𝔽)
    (hτ : RightInverse τ (ideleClassNorm F)) (χ : Chars(τ))
    (hWeil : PrimeFreeWeilIdentity χ.val)
    (hQ : ∀ k, ConditionalOutputOrder.QuotientNuclear (φχ(χ.val)) k)
    (U : ℕ → Set C𝔽) (hU : IsDPrimeSequence μ𝔽 U) (hBorel : ∀ n, MeasurableSet (U n)) :
    let J (k : ℕ) := primeFreeCenteredIntegral χ.val k (hQ k) U
    (∀ k : ℕ, J k - primeFreeArchConductor χ.val =
      exteriorMass(χ.val) + remainingOrder(χ.val,k)) ∧
    Tendsto (fun k ↦ J k - primeFreeArchConductor χ.val) atTop (𝓝 (exteriorMass(χ.val))) ∧
    ((∀ δ : ℝ, 0 < δ → ∃ k : ℕ, J k ≤ primeFreeArchConductor χ.val + δ) ↔
      ∀ z : Sites(χ.val), centered(z.val)) ∧
    ((limUnder atTop J ≤ primeFreeArchConductor χ.val) ↔ ∀ z : Sites(χ.val), centered(z.val)) := by
  have hoff := primeFreeCharacterTest_outside τ hτ χ
  exact primeFree_cappedComparison τ hτ χ hWeil
    (fun k ↦ primeFreeCenteredIntegral χ.val k (hQ k) U)
    (fun k ↦ ConditionalOutputOrder.centeredIntegral_re_eq τ hτ χ (φχ(χ.val)) hoff k
      (hQ k) U hU hBorel)
    (ConditionalOutputOrder.tendsto_centeredLineOrderDiagonal τ hτ χ (φχ(χ.val)) hoff hQ U hU hBorel)

/-- Paper: Theorem 12.5.1.1, pp. 519–520. One Borel smoothing sequence works
for every norm section. Given the fixed-test Weil identity and the stated
quotient nuclearity, both upper comparisons on the actual centered integrals
are equivalent to the exterior-zero sum for all allowed tests and all positive widths. -/
theorem exists_measurableSequence_archConductor_linePA_iff_exteriorZeros_of_weil_nuclear :
    ∃ U : ℕ → Set C𝔽, IsDPrimeSequence μ𝔽 U ∧ (∀ n, MeasurableSet (U n)) ∧
    ∀ (τ : ℝ≥0ˣ →ₜ* C𝔽), RightInverse τ (ideleClassNorm F) →
      (∀ χ : Chars(τ), PrimeFreeWeilIdentity χ.val) →
      ∀ hQ : ∀ (χ : Chars(τ)) (k : ℕ), ConditionalOutputOrder.QuotientNuclear (φχ(χ.val)) k,
        ((∀ (χ : Chars(τ)) (δ : ℝ), 0 < δ → ∃ k : ℕ,
          primeFreeCenteredIntegral χ.val k (hQ χ k) U ≤ primeFreeArchConductor χ.val + δ) ↔ target(τ)) ∧
        ((∀ χ : Chars(τ), limUnder atTop (fun k ↦ primeFreeCenteredIntegral χ.val k (hQ χ k) U)
          ≤ primeFreeArchConductor χ.val) ↔ target(τ)) := by
  obtain ⟨U,hU,hBorel⟩ := exists_measurable_ideleClassDPrimeSequence F
  refine ⟨U,hU,hBorel,?_⟩
  intro τ hτ hWeil hQ
  have hrow (χ : Chars(τ)) := primeFree_centeredComparison_of_weil_nuclear τ hτ χ
    (hWeil χ) (hQ χ) U hU hBorel
  exact ⟨(forall_congr' (fun χ ↦ (hrow χ).2.2.1)).trans (allCentral_iff_exteriorZeros τ hτ),
    (forall_congr' (fun χ ↦ (hrow χ).2.2.2)).trans (allCentral_iff_exteriorZeros τ hτ)⟩


attribute [local instance] instSpectralQuotientPolynormableSec3 in
/-- The prescribed polar-free test acts nuclearly on the true quotient at every
line order used in the centered comparison, for every angular character. -/
theorem primeFreeCharacterTest_quotientNuclear (χ : PontryaginDual C𝔽) (k : ℕ) :
    ConditionalOutputOrder.QuotientNuclear (φχ(χ)) k := by
  let row : PontryaginDual C₁ := χ.comp ⟨(ideleClassNorm F).ker.subtype, continuous_subtype_val⟩
  have hφ (u : C₁) (x : C𝔽) : (φχ(χ)).val (u.val⁻¹ * x) = (row u : ℂ) * (φχ(χ)).val x := by
    have hn : ideleClassNorm F (u.val⁻¹ * x) = ideleClassNorm F x := by
      rw [map_mul, map_inv, show ideleClassNorm F u.val = 1 from u.property, inv_one, one_mul]
    have hl : logIdeleClassNorm F (u.val⁻¹ * x) = logIdeleClassNorm F x :=
      congrArg (fun t : ℝ≥0ˣ ↦ Real.log (t.val : ℝ)) hn
    rw [primeFreeCharacterTest_apply, primeFreeCharacterTest_apply, hl]
    change (((χ (u.val⁻¹ * x))⁻¹ : Circle) : ℂ) * _ =
      (χ u.val : ℂ) * ((((χ x)⁻¹ : Circle) : ℂ) * (primeFreeProfile (logIdeleClassNorm F x) : ℂ))
    rw [map_mul, map_inv, mul_inv_rev, inv_inv, Circle.coe_mul]
    ring
  have hs := ConditionalOutputOrder.one_lt_degree k
  have hline (l : ℝ) (hl : l = 0) (hI : l ≤ 0) :
      IsNuclearOperator (spectralConvolution (F := F) (1/2) hI
        (zero_lt_one.trans hs).le (φχ(χ))) := by
    subst l
    exact spectralLineConvolution_homogeneous_nuclear (1/2) hs row (φχ(χ)) hφ
  exact hline (-0) neg_zero _

/-- Given the numerical Weil identity for the prescribed test, each of the two
upper comparisons over the odd Sobolev orders is equivalent to the all-test
exterior-zero assertion of Theorem 12.5.1.1, pp. 519–520. -/
theorem exists_measurableSequence_archConductor_linePA_iff_exteriorZeros_of_weil :
    ∃ U : ℕ → Set C𝔽, IsDPrimeSequence μ𝔽 U ∧ (∀ n, MeasurableSet (U n)) ∧
    ∀ (τ : ℝ≥0ˣ →ₜ* C𝔽), RightInverse τ (ideleClassNorm F) →
      (∀ χ : Chars(τ), PrimeFreeWeilIdentity χ.val) →
        ((∀ (χ : Chars(τ)) (δ : ℝ), 0 < δ → ∃ k : ℕ,
          primeFreeCenteredIntegral χ.val k (primeFreeCharacterTest_quotientNuclear χ.val k) U
            ≤ primeFreeArchConductor χ.val + δ) ↔ target(τ)) ∧
        ((∀ χ : Chars(τ), limUnder atTop (fun k ↦ primeFreeCenteredIntegral χ.val k
          (primeFreeCharacterTest_quotientNuclear χ.val k) U) ≤ primeFreeArchConductor χ.val) ↔
            target(τ)) := by
  obtain ⟨U,hU,hB,hw⟩ := exists_measurableSequence_archConductor_linePA_iff_exteriorZeros_of_weil_nuclear
    (F := F)
  exact ⟨U,hU,hB,fun τ hτ hWeil ↦ hw τ hτ hWeil fun χ k ↦
    primeFreeCharacterTest_quotientNuclear χ.val k⟩

end RiemannMasullo.Isolated.OutputOrderGeometry
