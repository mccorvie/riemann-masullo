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

section QuotientReturns

local notation "half" => (1 / 2 : ℝ)
local notation "W" => CompactIntervalSobolev μ𝔽 (logIdeleClassNorm F) (-half) half 0
local notation "hI" => (show -half ≤ half by norm_num)
local notation "Θ" => globalThetaSobolev F (1 / 2) hI (le_refl (0 : ℝ))
local notation "T" => hardySobolevTranslation μ𝔽 m𝔽 (-half) half 0 hI (le_refl (0 : ℝ))

/-- Reconstruction: A sufficient approximation property for Theorem 12.5.1.1,
pp. 519–520, using the degree-zero Mellin functionals of §10.2 on the critical
strip. Representatives with arbitrarily small rescaled translates modulo theta
span a dense subspace. The power can depend on the vector and tolerance. -/
def TotalThetaQuotientReturns (g : C𝔽) (α : ℝ) : Prop :=
  (Submodule.span ℂ {x : W | ∀ ε : ℝ, 0 < ε → ∃ n : ℕ,
    ‖(Θ).mkQ (T (g ^ n) x)‖ < ε * Real.exp (α * n)}).topologicalClosure = ⊤

/-- The order-zero jet of an interior zero gives a nonzero continuous Mellin
functional on the critical strip that vanishes on theta. -/
private theorem exteriorZero_mellinFunctional (ψ : PontryaginDual C𝔽) (b t : ℝ)
    (hb : b ∈ Ioo (-half) half)
    (hz : 0 < (meromorphicOrderAt (continuedCompletedHeckeL ψ)
      ((1 / 2 + b : ℝ) + (t : ℂ) * Complex.I)).untop₀) :
    ∃ L : W →L[ℂ] ℂ, L ≠ 0 ∧ Θ ≤ L.ker ∧ ∀ g x,
      L (T g x) = ideleClassNormTwist ψ ((b : ℂ) + (t : ℂ) * Complex.I) g * L x := by
  let χ : PontryaginDual C₁ → PontryaginDual C𝔽 := fun _ ↦ ψ
  let j : SpectralStripJetIndex χ half half 0 :=
    ⟨(1, b, t, 0), by
      change 0 < spectralStripMultiplicity half 0 b _
      rw [spectralStripMultiplicity_interior hb]
      change 0 < (meromorphicOrderAt (continuedCompletedHeckeL ψ)
        ((1 / 2 + b : ℝ) + (t : ℂ) * Complex.I)).untop₀.toNat
      omega⟩
  have hLp := spectralStripJet_memLp χ (show 0 ≤ half by norm_num) (le_refl 0) j
  let u := hLp.toLp _
  let D := (modulatedIntervalSobolev_dual m𝔽
    ⟨isProperMap_ideleClassNorm F, ideleClassNorm_ne_one (F := F)⟩ μ𝔽 (-half) half 0 hI (le_refl 0)).exists.choose
  let L := D.symm u
  have hp (x : W) : L x = spectralSobolevPairing x u :=
    (spectralSobolevPairing_dual hI (le_refl 0) L x).2.trans
      (congrArg (spectralSobolevPairing x) (D.apply_symm_apply u))
  let c := ideleClassNormTwist ψ ((b : ℂ) + (t : ℂ) * Complex.I)
  let w (g : C𝔽) := intervalSobolevDensity (-half) half 0 (logIdeleClassNorm F g)
  have hw : Measurable w := by
    have hD : Continuous (intervalSobolevDensity (-half) half 0) := by unfold intervalSobolevDensity; fun_prop
    exact hD.measurable.comp ((NNReal.continuous_coe.comp
      (Units.continuous_val.comp (isProperMap_ideleClassNorm F).continuous)).measurable.log)
  have hac : μ𝔽 ≪ (μ𝔽).withDensity (fun g ↦ ENNReal.ofReal (w g)⁻¹) := by
    refine withDensity_absolutelyContinuous' hw.inv.ennreal_ofReal.aemeasurable (.of_forall fun g ↦ ?_)
    exact ENNReal.ofReal_ne_zero_iff.mpr (inv_pos.mpr
      (mul_pos (lt_max_of_lt_left (Real.exp_pos _)) (Real.rpow_pos_of_pos (by positivity) _)))
  have hu : (u : C𝔽 → ℂ) =ᵐ[μ𝔽] ⇑c := by
    filter_upwards [hac.ae_le (MemLp.coeFn_toLp hLp)] with g hg
    exact hg.trans (by simp [j, χ, spectralZeroJet, c])
  have he (x : W) : L x = ∫ y, x y * c y ∂μ𝔽 :=
    (hp x).trans (integral_congr_ae (hu.mono fun y hy ↦ congrArg (x y * ·) hy))
  refine ⟨L, ?_, fun x hx ↦ (hp x).trans (spectralStripJet_commonKernel_forward χ
    (by norm_num : 0 ≤ half) (le_refl 0) x hx j), fun g x ↦ ?_⟩
  · intro h
    have h0 : u = 0 := (D.apply_symm_apply u).symm.trans (by change D L = 0; rw [h, map_zero])
    rw [h0] at hu
    have hn : (fun _ : C𝔽 ↦ (0 : ℂ)) =ᵐ[μ𝔽] ⇑c := (hac.ae_eq (Lp.coeFn_zero ℂ 2 _).symm).trans hu
    obtain ⟨y, hy⟩ := hn.exists
    change 0 = c y at hy
    have h1 := map_mul c y y⁻¹
    simp [← hy] at h1
  · let H (y : C𝔽) := x (g⁻¹ * y) * c y
    calc
      _ = ∫ y, H y ∂μ𝔽 := (he _).trans (integral_congr_ae
        ((hardySobolevTranslation_apply μ𝔽 m𝔽 (-half) half 0 hI (le_refl 0) g x).mono
          fun y hy ↦ congrArg (· * c y) hy))
      _ = ∫ y, H (g * y) ∂μ𝔽 := (integral_mul_left_eq_self H g).symm
      _ = c g * L x := by
        rw [he, ← integral_const_mul]
        simp only [H, inv_mul_cancel_left, map_mul]
        exact integral_congr_ae (.of_forall fun _ ↦ mul_left_comm ..)

private theorem norm_exteriorZero_twist (ψ : PontryaginDual C𝔽) (b t : ℝ) (g : C𝔽) :
    ‖ideleClassNormTwist ψ ((b : ℂ) + (t : ℂ) * Complex.I) g‖ = Real.exp (b * logIdeleClassNorm F g) := by
  have hg : 0 < ((ideleClassNorm F g).val : ℝ) := NNReal.coe_pos.mpr (Units.zero_lt _)
  change ‖(ψ g : ℂ) * (((ideleClassNorm F g).val : ℝ) : ℂ) ^ ((b : ℂ) + (t : ℂ) * Complex.I)‖ = _
  rw [norm_mul, Circle.norm_coe, one_mul, Complex.norm_cpow_eq_rpow_re_of_pos hg]
  simp [Real.rpow_def_of_pos hg, logIdeleClassNorm, mul_comm]

private theorem totalThetaQuotientReturns_excludes (g : C𝔽) {α : ℝ} (hd : TotalThetaQuotientReturns g α)
    (L : W →L[ℂ] ℂ) (hk : Θ ≤ L.ker) (c : C𝔽 →ₜ* ℂ)
    (he : ∀ h x, L (T h x) = c h * L x) (hg : Real.exp α ≤ ‖c g‖) : L = 0 := by
  let E := (Θ).liftQL L hk
  suffices hker : (⊤ : Submodule ℂ W) ≤ L.ker by
    ext x
    exact hker (Submodule.mem_top : x ∈ (⊤ : Submodule ℂ W))
  rw [← hd]
  apply Submodule.topologicalClosure_minimal _ _ L.isClosed_ker
  apply Submodule.span_le.mpr
  intro v hv
  change L v = 0
  by_contra h
  have hK : 0 < ‖E‖ + 1 := by positivity
  obtain ⟨n, hn⟩ := hv (‖L v‖ / (‖E‖ + 1)) (div_pos (norm_pos_iff.mpr h) hK)
  have hpow : Real.exp (α * n) ≤ ‖c (g ^ n)‖ := by
    rw [map_pow, norm_pow, mul_comm, Real.exp_nat_mul]
    exact pow_le_pow_left₀ (Real.exp_pos _).le hg _
  have hbound := E.le_opNorm ((Θ).mkQ (T (g ^ n) v))
  change ‖L (T (g ^ n) v)‖ ≤ _ at hbound
  rw [he, norm_mul] at hbound
  apply lt_irrefl (Real.exp (α * n) * ‖L v‖)
  calc
    _ ≤ ‖c (g ^ n)‖ * ‖L v‖ := mul_le_mul_of_nonneg_right hpow (norm_nonneg _)
    _ ≤ ‖E‖ * _ := hbound
    _ ≤ (‖E‖ + 1) * _ := mul_le_mul_of_nonneg_right (le_add_of_nonneg_right zero_le_one) (norm_nonneg _)
    _ < (‖E‖ + 1) * ((‖L v‖ / (‖E‖ + 1)) * Real.exp (α * n)) := mul_lt_mul_of_pos_left hn hK
    _ = _ := by rw [← mul_assoc, mul_div_cancel₀ _ hK.ne', mul_comm]

private theorem exteriorZero_order_reflect (ψ : PontryaginDual C𝔽) (ρ : ℂ) :
    meromorphicOrderAt (continuedCompletedHeckeL ψ⁻¹) (1 - ρ) =
      meromorphicOrderAt (continuedCompletedHeckeL ψ) ρ := by
  obtain ⟨hL, hLh⟩ := continuedCompletedHeckeL_spec ψ
  obtain ⟨hD, hDh⟩ := continuedCompletedHeckeL_spec ψ⁻¹
  obtain ⟨ε, hε, hne, hfe⟩ := completedHeckeL_continuation_functionalEquation ψ _ _ hL hLh hD hDh
  have hc : meromorphicOrderAt (fun s ↦ continuedCompletedHeckeL ψ⁻¹ (1 - s)) ρ =
      meromorphicOrderAt (continuedCompletedHeckeL ψ⁻¹) (1 - ρ) := by
    simpa [Function.comp_def] using
      meromorphicOrderAt_comp_of_deriv_ne_zero (f := continuedCompletedHeckeL ψ⁻¹)
        (show AnalyticAt ℂ (fun s : ℂ ↦ 1 - s) ρ by fun_prop)
        (show deriv (fun s : ℂ ↦ 1 - s) ρ ≠ 0 by simp)
  rw [← hc, show (fun s ↦ continuedCompletedHeckeL ψ⁻¹ (1 - s)) = ε * continuedCompletedHeckeL ψ
    from funext hfe, meromorphicOrderAt_mul_of_ne_zero (hε.analyticAt ρ) (hne ρ)]

local notation "extZeros(" τ ", " α ")" =>
  {z : {ψ : PontryaginDual C𝔽 // ∀ t : ℝ≥0ˣ, ψ (τ t) = 1} × ℂ //
    0 < MeromorphicOn.divisor (continuedCompletedHeckeL z.1.val) univ z.2 ∧ α ≤ |z.2.re - 1 / 2|}

/-- Paper: Theorem 12.5.1.1, pp. 519–520. For a family with dense linear span, small
rescaled returns modulo theta along positive powers of one dilation imply the
exterior-zero identity at the target half-width. A right-hand zero, including an
edge zero, puts every returning vector in the kernel of a nonzero functional.
The functional equation handles the left edge. -/
theorem traceFormula_exteriorZeros_of_totalThetaQuotientReturns
    (τ : ℝ≥0ˣ →ₜ* C𝔽) (hτ : Function.RightInverse τ (ideleClassNorm F))
    (g : C𝔽) (hg : logIdeleClassNorm F g = 1) {α : ℝ}
    (hd : TotalThetaQuotientReturns g α) (φ : BruhatCompactSupport C𝔽) :
    HasSum (fun z : extZeros(τ, α) ↦
      ((MeromorphicOn.divisor (continuedCompletedHeckeL z.val.1.val) univ z.val.2 : ℤ) : ℂ) *
        modulatedFourierMellin m𝔽 univ ⟨isProperMap_ideleClassNorm F, ideleClassNorm_ne_one (F := F)⟩
          μ𝔽 φ.val (ideleClassNormTwist z.val.1.val (z.val.2 - 1 / 2))) 0 := by
  have right (ψ : PontryaginDual C𝔽) (ρ : ℂ) (hb : ρ.re - 1 / 2 ∈ Ioo (-half) half)
      (hz : 0 < (meromorphicOrderAt (continuedCompletedHeckeL ψ) ρ).untop₀)
      (hα : α ≤ ρ.re - 1 / 2) : False := by
    let b := ρ.re - 1 / 2
    have hρ : ((1 / 2 + b : ℝ) : ℂ) + (ρ.im : ℂ) * Complex.I = ρ := by
      rw [show (1 / 2 : ℝ) + b = ρ.re by dsimp [b]; ring, Complex.re_add_im]
    obtain ⟨L, hL, hk, he⟩ := exteriorZero_mellinFunctional ψ b ρ.im hb (by rwa [hρ])
    apply hL (totalThetaQuotientReturns_excludes g hd L hk _ he ?_)
    rw [norm_exteriorZero_twist, hg, mul_one, Real.exp_le_exp]
    exact hα
  suffices hempty : IsEmpty extZeros(τ, α) by exact hasSum_empty
  constructor
  rintro ⟨⟨ψ, ρ⟩, hz, hα⟩
  have hwide := (hasSum_exteriorZeros_iff_isEmpty τ hτ (1 / 2)).mp
    (fun f _ ↦ traceFormula_exteriorZeros_of_half_le τ f le_rfl)
  have hb : |ρ.re - 1 / 2| < 1 / 2 := lt_of_not_ge fun h ↦ hwide.false ⟨(ψ, ρ), hz, h⟩
  rw [MeromorphicOn.divisor_apply (continuedCompletedHeckeL_spec ψ.val).1.meromorphicOn (mem_univ _)] at hz
  rcases le_total 0 (ρ.re - 1 / 2) with h | h
  · exact right ψ.val ρ (abs_lt.mp hb) hz (by rwa [abs_of_nonneg h] at hα)
  · apply right ψ.val⁻¹ (1 - ρ)
    · rw [Complex.sub_re, Complex.one_re]
      exact ⟨by linarith [(abs_lt.mp hb).2], by linarith [(abs_lt.mp hb).1]⟩
    · rwa [exteriorZero_order_reflect]
    · rw [abs_of_nonpos h] at hα
      rw [Complex.sub_re, Complex.one_re]
      linarith

end QuotientReturns

end RiemannMasullo.Isolated
