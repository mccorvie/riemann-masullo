module

import Mathlib.Geometry.Manifold.PartitionOfUnity
import RiemannMasullo.Ch10_TraceSpectral.Sec4b_ProjectedKernels
public import RiemannMasullo.Ch12_TraceGeometric.Sec5

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

/-! ## Contractive transport between strip widths

The narrowing map preserves the closed theta spaces. The resulting change of
spectral projection energy splits into the weight change and an orthogonal loss.
This is a global comparison for the strip projections in Theorem 12.5.1.1.
-/

namespace RiemannMasullo.Isolated

open scoped InnerProductSpace

section AbstractTransport

variable {𝕜 H₀ H₁ : Type*} [RCLike 𝕜]
  [NormedAddCommGroup H₀] [InnerProductSpace 𝕜 H₀]
  [NormedAddCommGroup H₁] [InnerProductSpace 𝕜 H₁]
  (Θ₀ : Submodule 𝕜 H₀) (Θ₁ : Submodule 𝕜 H₁)
  [Θ₀.HasOrthogonalProjection] [Θ₁.HasOrthogonalProjection]
  (J : H₁ →L[𝕜] H₀)

/-- Transport that preserves the theta spaces can discard the wider theta
component before taking the narrower complementary projection. -/
private theorem starProjection_orthogonal_transport_apply (hJ : ∀ x ∈ Θ₁, J x ∈ Θ₀) (x : H₁) :
    Θ₀ᗮ.starProjection (J x) = Θ₀ᗮ.starProjection (J (Θ₁ᗮ.starProjection x)) := by
  have hx : x - Θ₁ᗮ.starProjection x ∈ Θ₁ := by
    rw [Θ₁.starProjection_orthogonal_val, sub_sub_cancel]
    exact (Θ₁.orthogonalProjectionOnto x).property
  have hzero := Θ₀.starProjection_orthogonal_apply_eq_zero (hJ _ hx)
  rw [map_sub, map_sub, sub_eq_zero] at hzero
  exact hzero

/-- The change of complementary projection energy splits into the norm change
under transport and the squared part removed by the narrower projection. -/
private theorem starProjection_orthogonal_transport_norm_sq_sub
    (hJ : ∀ x ∈ Θ₁, J x ∈ Θ₀) (x : H₁) :
    let P₀ := Θ₀ᗮ.starProjection
    let P₁ := Θ₁ᗮ.starProjection
    ‖P₁ x‖ ^ 2 - ‖P₀ (J x)‖ ^ 2 =
      (‖P₁ x‖ ^ 2 - ‖J (P₁ x)‖ ^ 2) + ‖J (P₁ x) - P₀ (J (P₁ x))‖ ^ 2 := by
  intro P₀ P₁
  have heq : P₀ (J x) = P₀ (J (P₁ x)) :=
    starProjection_orthogonal_transport_apply Θ₀ Θ₁ J hJ x
  have hpyth := Θ₀ᗮ.norm_sq_eq_add_norm_sq_starProjection (J (P₁ x))
  rw [Θ₀ᗮ.starProjection_orthogonal_val] at hpyth
  change ‖J (P₁ x)‖ ^ 2 = ‖P₀ (J (P₁ x))‖ ^ 2 + ‖J (P₁ x) - P₀ (J (P₁ x))‖ ^ 2 at hpyth
  rw [heq]
  linarith

/-- Under contractive transport, the orthogonal loss is a lower bound for the
whole decrease in complementary projection energy. -/
private theorem starProjection_orthogonal_transport_norm_sq_sub_ge
    (hJ : ∀ x ∈ Θ₁, J x ∈ Θ₀) (hcontract : ‖J‖ ≤ 1) (x : H₁) :
    let P₀ := Θ₀ᗮ.starProjection
    let P₁ := Θ₁ᗮ.starProjection
    ‖J (P₁ x) - P₀ (J (P₁ x))‖ ^ 2 ≤ ‖P₁ x‖ ^ 2 - ‖P₀ (J x)‖ ^ 2 := by
  intro P₀ P₁
  have hnorm : ‖J (P₁ x)‖ ≤ ‖P₁ x‖ :=
    (J.le_opNorm _).trans (mul_le_of_le_one_left (norm_nonneg _) hcontract)
  have hsquare := pow_le_pow_left₀ (norm_nonneg _) hnorm 2
  rw [starProjection_orthogonal_transport_norm_sq_sub Θ₀ Θ₁ J hJ x]
  linarith

/-- A test vector from the narrower theta space gives a Cauchy–Schwarz lower
bound for the compression loss, without division by its squared norm. -/
private theorem starProjection_orthogonal_transport_inner_norm_sq_le
    (hJ : ∀ x ∈ Θ₁, J x ∈ Θ₀) (hcontract : ‖J‖ ≤ 1) (x : H₁) {u : H₀} (hu : u ∈ Θ₀) :
    let P₀ := Θ₀ᗮ.starProjection
    let P₁ := Θ₁ᗮ.starProjection
    ‖⟪u, J (P₁ x)⟫_𝕜‖ ^ 2 ≤ ‖u‖ ^ 2 * (‖P₁ x‖ ^ 2 - ‖P₀ (J x)‖ ^ 2) := by
  intro P₀ P₁
  let y := J (P₁ x)
  have hz : ⟪u, P₀ y⟫_𝕜 = 0 :=
    Submodule.inner_right_of_mem_orthogonal hu (Θ₀ᗮ.starProjection_apply_mem y)
  have heq : ⟪u, y - P₀ y⟫_𝕜 = ⟪u, y⟫_𝕜 := by rw [inner_sub_right, hz, sub_zero]
  calc
    ‖⟪u, y⟫_𝕜‖ ^ 2 ≤ (‖u‖ * ‖y - P₀ y‖) ^ 2 := by
      rw [← heq]
      exact pow_le_pow_left₀ (norm_nonneg _) (norm_inner_le_norm _ _) 2
    _ = ‖u‖ ^ 2 * ‖y - P₀ y‖ ^ 2 := mul_pow _ _ _
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (starProjection_orthogonal_transport_norm_sq_sub_ge Θ₀ Θ₁ J hJ hcontract x)
      (sq_nonneg _)

end AbstractTransport

section GlobalStripTransport

open Filter MeasureTheory NumberField Set
open scoped ENNReal

attribute [local instance] instIdeleClassMeasurableSpaceSec1 instIdeleClassBorelSpaceSec1
  instIdeleClassT2Sec1 instIdeleClassLocallyCompactSec1 instIdeleClassSecondCountableSec1
  instIdeleClassHaarMeasureSec1

variable {F : Type*} [Field F] [NumberField F]

local notation "C𝔽" => IdeleClassGroup (𝓞 F) F
local notation "μ𝔽" => ideleClassTamagawaMeasure F
local notation "W(" c ", " s ")" => CompactIntervalSobolev μ𝔽 (logIdeleClassNorm F) (-c) c s
local notation "ν(" c ", " s ")" => intervalSobolevMeasure μ𝔽 (logIdeleClassNorm F) (-c) c s
local notation "Θ(" a ", " hc ", " hs ")" => globalThetaSobolev F a (neg_le_self hc) hs

private theorem intervalDensity_symmetric_mono {α β : ℝ} (hα : 0 ≤ α) (hαβ : α ≤ β) (s t : ℝ) :
    intervalSobolevDensity (-α) α s t ≤ intervalSobolevDensity (-β) β s t := by
  have hβ := hα.trans hαβ
  unfold intervalSobolevDensity
  apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (by positivity) _)
  rcases le_total t 0 with ht | ht
  · have hneg : 2 * (-α) * t ≤ 2 * (-β) * t :=
      mul_le_mul_of_nonpos_right (mul_le_mul_of_nonneg_left (neg_le_neg hαβ) zero_le_two) ht
    have hpos : 2 * α * t ≤ 2 * (-β) * t :=
      mul_le_mul_of_nonpos_right (by linarith) ht
    exact max_le ((Real.exp_le_exp.mpr hneg).trans (le_max_left _ _))
      ((Real.exp_le_exp.mpr hpos).trans (le_max_left _ _))
  · have hneg : 2 * (-α) * t ≤ 2 * β * t :=
      mul_le_mul_of_nonneg_right (by linarith) ht
    have hpos : 2 * α * t ≤ 2 * β * t :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hαβ zero_le_two) ht
    exact max_le ((Real.exp_le_exp.mpr hneg).trans (le_max_right _ _))
      ((Real.exp_le_exp.mpr hpos).trans (le_max_right _ _))

/-- Narrowing the symmetric strip at fixed order and twist preserves the
weighted theta generators of Definition 10.1.1.1(1), p. 434, and their closure. -/
theorem exists_globalThetaSobolev_widthTransport (a : ℝ) {α β s : ℝ}
    (hα : 0 ≤ α) (hαβ : α ≤ β) (hs : 0 ≤ s) :
    ∃ J : W(β, s) →L[ℂ] W(α, s), ‖J‖ ≤ 1 ∧
      (∀ x, (J x : C𝔽 → ℂ) =ᵐ[ν(α, s)] (x : C𝔽 → ℂ)) ∧
      ∀ x ∈ Θ(a, hα.trans hαβ, hs), J x ∈ Θ(a, hα, hs) := by
  have hβ := hα.trans hαβ
  have hle : ν(α, s) ≤ ν(β, s) :=
    withDensity_mono (ae_of_all _ fun g ↦ ENNReal.ofReal_le_ofReal
      (intervalDensity_symmetric_mono hα hαβ s (logIdeleClassNorm F g)))
  have hle' : ν(α, s) ≤ (1 : ℝ≥0∞) • ν(β, s) := by simpa only [one_smul] using hle
  let L : W(β, s) →L[ℝ] W(α, s) :=
    Lp.LpToLpOfMeasureLeSMul (E := ℂ) (p := 2) ENNReal.one_ne_top hle'
  have hL (x : W(β, s)) : (L x : C𝔽 → ℂ) =ᵐ[ν(α, s)] (x : C𝔽 → ℂ) :=
    Lp.coeFn_LpToLpOfMeasureLeSMul ENNReal.one_ne_top hle' x
  let J : W(β, s) →L[ℂ] W(α, s) :=
    { toFun := L
      map_add' := L.map_add
      map_smul' := fun c x ↦ Lp.ext <|
        (hL (c • x)).trans (Filter.EventuallyEq.trans (ae_mono hle (Lp.coeFn_smul c x))
          (((hL x).symm.fun_comp (c • ·)).trans (Lp.coeFn_smul c (L x)).symm))
      cont := L.continuous }
  have hJ (x : W(β, s)) : (J x : C𝔽 → ℂ) =ᵐ[ν(α, s)] (x : C𝔽 → ℂ) := hL x
  refine ⟨J, ?_, hJ, ?_⟩
  · rw [← ContinuousLinearMap.norm_restrictScalars (𝕜' := ℝ) J]
    change ‖L‖ ≤ 1
    simpa only [ENNReal.toReal_one, Real.one_rpow] using
      Lp.norm_LpToLpOfMeasureLeSMul_le (E := ℂ) (p := 2) ENNReal.one_ne_top hle'
  · let Eα := (existsUnique_globalThetaSobolevEmbedding (F := F) a (-α) α s
      (neg_le_self hα) hs).exists.choose
    let Eβ := (existsUnique_globalThetaSobolevEmbedding (F := F) a (-β) β s
      (neg_le_self hβ) hs).exists.choose
    have hgen (q) : J (Eβ q) = Eα q := by
      induction q using Submodule.Quotient.induction_on with
      | _ f =>
        have hfα := (existsUnique_globalThetaSobolevEmbedding (F := F) a (-α) α s
          (neg_le_self hα) hs).exists.choose_spec.2 f
        have hfβ := (existsUnique_globalThetaSobolevEmbedding (F := F) a (-β) β s
          (neg_le_self hβ) hs).exists.choose_spec.2 f
        exact Lp.ext ((hJ _).trans ((withDensity_absolutelyContinuous _ _).ae_eq
          (hfβ.trans hfα.symm)))
    intro x hx
    change x ∈ closure (Set.range Eβ) at hx
    change J x ∈ closure (Set.range Eα)
    have himage : J '' Set.range Eβ ⊆ Set.range Eα := by
      rintro _ ⟨_, ⟨q, rfl⟩, rfl⟩
      exact ⟨q, (hgen q).symm⟩
    exact closure_mono himage
      (image_closure_subset_closure_image J.continuous (Set.mem_image_of_mem J hx))

/-- The spectral projections of Definition 10.4.1.1(2), p. 456, satisfy a
two-term energy identity under the canonical narrowing transport. The orthogonal
loss and the pairing with a narrower theta vector give lower bounds for the
energy decrease. -/
theorem exists_spectralProjection_widthTransport_norm_sq_sub (a : ℝ) {α β s : ℝ}
    (hα : 0 ≤ α) (hαβ : α ≤ β) (hs : 0 ≤ s) :
    ∃ J : W(β, s) →L[ℂ] W(α, s), ‖J‖ ≤ 1 ∧
      (∀ x, (J x : C𝔽 → ℂ) =ᵐ[ν(α, s)] (x : C𝔽 → ℂ)) ∧
      ∀ x, let Pα := spectralProjection (F := F) a hα hs
           let Pβ := spectralProjection (F := F) a (hα.trans hαβ) hs
           (‖Pβ x‖ ^ 2 - ‖Pα (J x)‖ ^ 2 =
             (‖Pβ x‖ ^ 2 - ‖J (Pβ x)‖ ^ 2) + ‖J (Pβ x) - Pα (J (Pβ x))‖ ^ 2) ∧
           ‖J (Pβ x) - Pα (J (Pβ x))‖ ^ 2 ≤ ‖Pβ x‖ ^ 2 - ‖Pα (J x)‖ ^ 2 ∧
           ∀ u ∈ Θ(a, hα, hs),
             ‖⟪u, J (Pβ x)⟫_ℂ‖ ^ 2 ≤ ‖u‖ ^ 2 * (‖Pβ x‖ ^ 2 - ‖Pα (J x)‖ ^ 2) := by
  have hβ := hα.trans hαβ
  obtain ⟨J, hJ, hrep, hmap⟩ := exists_globalThetaSobolev_widthTransport (F := F) a hα hαβ hs
  let : CompleteSpace Θ(a, hα, hs) :=
    (globalThetaSobolev_closed_complete_separable (F := F) a (neg_le_self hα) hs).2.1
  let : CompleteSpace Θ(a, hβ, hs) :=
    (globalThetaSobolev_closed_complete_separable (F := F) a (neg_le_self hβ) hs).2.1
  exact ⟨J, hJ, hrep, fun x ↦ ⟨
    starProjection_orthogonal_transport_norm_sq_sub Θ(a, hα, hs) Θ(a, hβ, hs) J hmap x,
    starProjection_orthogonal_transport_norm_sq_sub_ge Θ(a, hα, hs) Θ(a, hβ, hs) J hmap hJ x,
    fun _u hu ↦ starProjection_orthogonal_transport_inner_norm_sq_le
      Θ(a, hα, hs) Θ(a, hβ, hs) J hmap hJ x hu⟩⟩

end GlobalStripTransport

end RiemannMasullo.Isolated
