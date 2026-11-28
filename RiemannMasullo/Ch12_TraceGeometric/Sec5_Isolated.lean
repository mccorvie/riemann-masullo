module

import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Geometry.Manifold.PartitionOfUnity
public import RiemannMasullo.Ch10_TraceSpectral.Sec4b_ProjectedKernels
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

section OrderZeroDiagonalComparison

open Function
open scoped NumberField.AdeleRing

/-- The Haar convolution kernel minus the projective spectral kernel at order zero. -/
def orderZeroProjectiveGeometricKernel
    (φ : BruhatCompactSupport C𝔽) {α : ℝ} (hα : 0 ≤ α) (p : C𝔽 × C𝔽) : ℂ :=
  let hK := stripTestAction_spectralProjection_has_projectiveKernel (F := F) (1 / 2)
    hα (s := 0) le_rfl φ
  φ.val (p.1 * p.2⁻¹) - sobolevProjectiveKernelClass (F := F) hα le_rfl hK.choose p

/-- Paper: Theorem 12.5.1.1, pp. 519–520. A comparison between the narrow and
wide order-zero geometric diagonals would prove the exact exterior cancellation
for this test and width, including both edges.
Gap: The signed global-to-local comparison in §12.3, p. 514, is needed to obtain
the equality of the Haar integrals. The measurable D′-sequence is supplied as data. -/
theorem traceFormula_exteriorZeros_of_orderZeroDiagonalWidthComparison
    (τ : ℝ≥0ˣ →ₜ* C𝔽) (hτ : RightInverse τ (ideleClassNorm F))
    (φ : BruhatCompactSupport C𝔽) (hφ : ∀ g : C₁, φ.val g = 0) {α : ℝ} (hα : 0 < α)
    (U : ℕ → Set C𝔽) (hU : IsDPrimeSequence μ𝔽 U) (hBorel : ∀ n, MeasurableSet (U n))
    (hComparison : (∫ x, dSequenceKernelSmoothening μ𝔽 U
        (orderZeroProjectiveGeometricKernel φ hα.le) (x, x) ∂μ𝔽) =
      ∫ x, dSequenceKernelSmoothening μ𝔽 U
        (orderZeroProjectiveGeometricKernel φ (by norm_num : (0 : ℝ) ≤ 1 / 2)) (x, x) ∂μ𝔽) :
    let Z := {z : {χ : PontryaginDual C𝔽 // ∀ t : ℝ≥0ˣ, χ (τ t) = 1} × ℂ //
      0 < MeromorphicOn.divisor (continuedCompletedHeckeL (F := F) z.1.val) univ z.2 ∧
        α ≤ |z.2.re - 1 / 2|}
    HasSum (fun z : Z ↦
      ((MeromorphicOn.divisor (continuedCompletedHeckeL (F := F) z.val.1.val) univ z.val.2 : ℤ) : ℂ) *
        modulatedFourierMellin m𝔽 univ ⟨isProperMap_ideleClassNorm F, ideleClassNorm_ne_one (F := F)⟩
          μ𝔽 φ.val (ideleClassNormTwist (F := F) z.val.1.val (z.val.2 - 1 / 2))) 0 := by
  intro Z
  have hwide : (0 : ℝ) < 1 / 2 := by norm_num
  obtain ⟨a, b, ha, hb, _, _⟩ := traceFormula_of_half_le τ hτ φ (le_refl (1 / 2 : ℝ))
  let hK := stripTestAction_spectralProjection_has_projectiveKernel (F := F) (1 / 2)
    hα.le (s := 0) le_rfl φ
  let hKwide := stripTestAction_spectralProjection_has_projectiveKernel (F := F) (1 / 2)
    hwide.le (s := 0) le_rfl φ
  have hφ1 : φ.val 1 = 0 := hφ 1
  have narrow := (hasSum_exteriorZeros_localTerms_add_smoothenedProjectiveGeometricDiagonal_of_le_one
    τ hτ hα le_rfl zero_le_one φ hφ1 a b ha hb hK.choose hK.choose_spec U hU hBorel).2
  have wide := (hasSum_exteriorZeros_localTerms_add_smoothenedProjectiveGeometricDiagonal_of_le_one
    τ hτ hwide le_rfl zero_le_one φ hφ1 a b ha hb hKwide.choose hKwide.choose_spec U hU hBorel).2
  have hz := wide.unique (traceFormula_exteriorZeros_of_half_le τ φ (le_refl (1 / 2 : ℝ)))
  change (∫ x, dSequenceKernelSmoothening μ𝔽 U
      (fun p : C𝔽 × C𝔽 ↦ φ.val (p.1 * p.2⁻¹) -
        sobolevProjectiveKernelClass (F := F) hα.le le_rfl hK.choose p) (x, x) ∂μ𝔽) =
    (∫ x, dSequenceKernelSmoothening μ𝔽 U
      (fun p : C𝔽 × C𝔽 ↦ φ.val (p.1 * p.2⁻¹) -
        sobolevProjectiveKernelClass (F := F) hwide.le le_rfl hKwide.choose p) (x, x) ∂μ𝔽)
    at hComparison
  rw [hComparison, hz] at narrow
  exact narrow

local notation "SectionCharacterPoint(" τ ")" =>
  ({χ : PontryaginDual C𝔽 // ∀ t : ℝ≥0ˣ, χ (τ t) = 1} × ℂ)
local notation "ord(" z ")" =>
  MeromorphicOn.divisor (continuedCompletedHeckeL (F := F) (z).1.val) univ (z).2
local notation "offset(" z ")" => |(z).2.re - 1 / 2|
local notation "zeroTerm(" φ ", " z ")" =>
  (((ord(z) : ℤ) : ℂ) * modulatedFourierMellin m𝔽 univ
    ⟨isProperMap_ideleClassNorm F, ideleClassNorm_ne_one (F := F)⟩
    μ𝔽 (φ : BruhatCompactSupport C𝔽).val (ideleClassNormTwist (F := F) (z).1.val ((z).2 - 1 / 2)))

/-- The Haar integral of the smoothed projective geometric diagonal at Sobolev order zero. -/
def orderZeroProjectiveGeometricTrace (φ : BruhatCompactSupport C𝔽) {α : ℝ} (hα : 0 ≤ α)
    (U : ℕ → Set C𝔽) : ℂ :=
  ∫ x, dSequenceKernelSmoothening μ𝔽 U (orderZeroProjectiveGeometricKernel φ hα) (x, x) ∂μ𝔽

/-- Paper: Theorem 12.5.1.1, pp. 519–520. The narrow-minus-wide order-zero
geometric traces give the signed sum of the zeros between the two widths.
The smaller boundary contributes in full, and the larger boundary does not contribute. -/
theorem hasSum_widthShell_orderZeroProjectiveGeometricTrace
    (τ : ℝ≥0ˣ →ₜ* C𝔽) (hτ : RightInverse τ (ideleClassNorm F))
    (φ : BruhatCompactSupport C𝔽) (hφ : φ.val 1 = 0) {α β : ℝ} (hα : 0 < α)
    (hαβ : α ≤ β) (U : ℕ → Set C𝔽) (hU : IsDPrimeSequence μ𝔽 U)
    (hBorel : ∀ n, MeasurableSet (U n)) :
    HasSum (fun z : {z : SectionCharacterPoint(τ) // 0 < ord(z) ∧ α ≤ offset(z) ∧ offset(z) < β} ↦
      zeroTerm(φ, z.val))
      (orderZeroProjectiveGeometricTrace φ hα.le U -
        orderZeroProjectiveGeometricTrace φ (hα.le.trans hαβ) U) := by
  classical
  have hβ : 0 < β := hα.trans_le hαβ
  obtain ⟨a, b, ha, hb, _, _⟩ := traceFormula_of_half_le τ hτ φ (le_refl (1 / 2 : ℝ))
  let hKα := stripTestAction_spectralProjection_has_projectiveKernel (F := F) (1 / 2)
    hα.le (s := 0) le_rfl φ
  let hKβ := stripTestAction_spectralProjection_has_projectiveKernel (F := F) (1 / 2)
    hβ.le (s := 0) le_rfl φ
  have narrow := (hasSum_exteriorZeros_localTerms_add_smoothenedProjectiveGeometricDiagonal_of_le_one
    τ hτ hα le_rfl zero_le_one φ hφ a b ha hb hKα.choose hKα.choose_spec U hU hBorel).2
  have wide := (hasSum_exteriorZeros_localTerms_add_smoothenedProjectiveGeometricDiagonal_of_le_one
    τ hτ hβ le_rfl zero_le_one φ hφ a b ha hb hKβ.choose hKβ.choose_spec U hU hBorel).2
  let A : Set SectionCharacterPoint(τ) := {p | 0 < ord(p) ∧ α ≤ offset(p)}
  let B : Set SectionCharacterPoint(τ) := {p | 0 < ord(p) ∧ β ≤ offset(p)}
  let S : Set SectionCharacterPoint(τ) := {p | 0 < ord(p) ∧ α ≤ offset(p) ∧ offset(p) < β}
  let term (p : SectionCharacterPoint(τ)) : ℂ := zeroTerm(φ, p)
  have hBA : B ⊆ A := fun p hp ↦ ⟨hp.1, hαβ.trans hp.2⟩
  have hS : S = A \ B := by
    ext p
    constructor
    · intro hp
      exact ⟨⟨hp.1, hp.2.1⟩, fun hb' ↦ (not_le_of_gt hp.2.2) hb'.2⟩
    · intro hp
      exact ⟨hp.1.1, hp.1.2, lt_of_not_ge fun hb' ↦ hp.2 ⟨hp.1.1, hb'⟩⟩
  refine (hasSum_subtype_iff_indicator (f := term) (s := S)).mpr ?_
  rw [hS, Set.indicator_sdiff' hBA term]
  have hA := (hasSum_subtype_iff_indicator (f := term) (s := A)).mp narrow
  have hB := (hasSum_subtype_iff_indicator (f := term) (s := B)).mp wide
  have h := hA.sub hB
  rw [add_sub_add_left_eq_sub] at h
  exact h

open Filter in
open scoped Topology in
/-- Paper: Theorem 12.5.1.1, pp. 519–520. Along any sequence of positive widths
converging to zero, the narrow-minus-wide order-zero geometric trace converges to the
full sum over the off-critical-line zeros for the test. -/
theorem hasSum_offCriticalZeros_orderZeroProjectiveGeometricTrace_limit
    (τ : ℝ≥0ˣ →ₜ* C𝔽) (hτ : RightInverse τ (ideleClassNorm F))
    (u : ℕ → ℝ) (hu : ∀ n, 0 < u n) (hlim : Tendsto u atTop (𝓝 0))
    (U : ℕ → Set C𝔽) (hU : IsDPrimeSequence μ𝔽 U) (hBorel : ∀ n, MeasurableSet (U n))
    (φ : BruhatCompactSupport C𝔽) (hφ : φ.val 1 = 0) :
    ∃ S : ℂ, HasSum (fun z : {z : SectionCharacterPoint(τ) // 0 < ord(z) ∧ 0 < offset(z)} ↦
      zeroTerm(φ, z.val)) S ∧
      Tendsto (fun n ↦ orderZeroProjectiveGeometricTrace φ (hu n).le U -
        orderZeroProjectiveGeometricTrace φ (by norm_num : (0 : ℝ) ≤ 1 / 2) U) atTop (𝓝 S) := by
  classical
  let Full := {z : SectionCharacterPoint(τ) // 0 < ord(z) ∧ offset(z) < 1 / 2}
  let term (z : Full) : ℂ := zeroTerm(φ, z.val)
  obtain ⟨_, _, _, _, _, hfull⟩ := traceFormula_of_half_le τ hτ φ (le_refl (1 / 2 : ℝ))
  have hs : Summable term := hfull.summable
  let truncatedTerm (n : ℕ) : Full → ℂ := fun z ↦ if u n ≤ offset(z.val) then term z else 0
  let offLineTerm : Full → ℂ := fun z ↦ if 0 < offset(z.val) then term z else 0
  have hterm (z : Full) : Tendsto (fun n ↦ truncatedTerm n z) atTop (𝓝 (offLineTerm z)) := by
    by_cases hz : 0 < offset(z.val)
    · have he : ∀ᶠ n in atTop, u n < offset(z.val) := hlim.eventually (Iio_mem_nhds hz)
      change Tendsto (fun n ↦ truncatedTerm n z) atTop (𝓝 (if 0 < offset(z.val) then term z else 0))
      rw [ite_eq_left hz]
      apply tendsto_const_nhds.congr'
      filter_upwards [he] with n hn
      change term z = (if u n ≤ offset(z.val) then term z else 0)
      rw [ite_eq_left hn.le]
    · have hz' : offset(z.val) = 0 := le_antisymm (not_lt.mp hz) (abs_nonneg _)
      have hoff : offLineTerm z = 0 := by
        change (if 0 < offset(z.val) then term z else 0) = 0
        exact ite_eq_right hz
      rw [hoff]
      apply tendsto_const_nhds.congr'
      filter_upwards with n
      change 0 = (if u n ≤ offset(z.val) then term z else 0)
      rw [hz', ite_eq_right (not_le_of_gt (hu n))]
  have hconv : Tendsto (fun n ↦ ∑' z, truncatedTerm n z) atTop (𝓝 (∑' z, offLineTerm z)) := by
    refine tendsto_tsum_of_dominated_convergence hs.norm hterm (Eventually.of_forall fun n z ↦ ?_)
    change ‖(if u n ≤ offset(z.val) then term z else 0)‖ ≤ ‖term z‖
    split_ifs <;> simp
  have htrace : (fun n ↦ ∑' z, truncatedTerm n z) =ᶠ[atTop]
      (fun n ↦ orderZeroProjectiveGeometricTrace φ (hu n).le U -
        orderZeroProjectiveGeometricTrace φ (by norm_num : (0 : ℝ) ≤ 1 / 2) U) := by
    filter_upwards [hlim.eventually (Iio_mem_nhds (show (0 : ℝ) < 1 / 2 by norm_num))] with n hn
    let A : Set Full := {z | u n ≤ offset(z.val)}
    let Shell := {z : SectionCharacterPoint(τ) // 0 < ord(z) ∧ u n ≤ offset(z) ∧ offset(z) < 1 / 2}
    let e : A ≃ Shell :=
      ⟨fun z ↦ ⟨z.val.val, z.val.property.1, z.property, z.val.property.2⟩,
        fun z ↦ ⟨⟨z.val, z.property.1, z.property.2.2⟩, z.property.2.1⟩,
        fun _ ↦ rfl, fun _ ↦ rfl⟩
    have h := hasSum_widthShell_orderZeroProjectiveGeometricTrace τ hτ φ hφ
      (hu n) hn.le U hU hBorel
    have h' := (e.hasSum_iff).mpr h
    have h'' := (hasSum_subtype_iff_indicator (s := A) (f := term)).mp h'
    change (∑' z, A.indicator term z) = _
    exact h''.tsum_eq
  let B : Set Full := {z | 0 < offset(z.val)}
  have hSB : Summable (fun z : B ↦ term z.val) := hs.subtype (fun z ↦ z ∈ B)
  have hSel : HasSum offLineTerm (∑' z : B, term z.val) :=
    (hasSum_subtype_iff_indicator (s := B) (f := term)).mp hSB.hasSum
  have hWideEmpty : IsEmpty {z : SectionCharacterPoint(τ) // 0 < ord(z) ∧ 1 / 2 ≤ offset(z)} :=
    (hasSum_exteriorZeros_iff_isEmpty τ hτ (1 / 2 : ℝ)).mp
      (fun ψ _ ↦ traceFormula_exteriorZeros_of_half_le τ ψ (le_refl (1 / 2 : ℝ)))
  have hhalf (z : SectionCharacterPoint(τ)) (hz : 0 < ord(z)) : offset(z) < 1 / 2 :=
    lt_of_not_ge fun h ↦ @IsEmpty.false _ hWideEmpty ⟨z, hz, h⟩
  let e : B ≃ {z : SectionCharacterPoint(τ) // 0 < ord(z) ∧ 0 < offset(z)} :=
    ⟨fun z ↦ ⟨z.val.val, z.val.property.1, z.property⟩,
      fun z ↦ ⟨⟨z.val, z.property.1, hhalf z.val z.property.1⟩, z.property.2⟩,
      fun _ ↦ rfl, fun _ ↦ rfl⟩
  refine ⟨_, (e.hasSum_iff).mp hSB.hasSum, ?_⟩
  rw [← hSel.tsum_eq]
  exact hconv.congr' htrace

open Filter in
open scoped Topology in
/-- Paper: Theorem 12.5.1.1, pp. 519–520. Testwise convergence to zero of the
order-zero geometric trace residuals along one sequence of positive widths implies
the exterior zero cancellation for every positive width. -/
theorem traceFormula_exteriorZeros_of_orderZeroProjectiveGeometricTrace_tendsto
    (τ : ℝ≥0ˣ →ₜ* C𝔽) (hτ : RightInverse τ (ideleClassNorm F))
    (u : ℕ → ℝ) (hu : ∀ n, 0 < u n) (hlim : Tendsto u atTop (𝓝 0))
    (U : ℕ → Set C𝔽) (hU : IsDPrimeSequence μ𝔽 U) (hBorel : ∀ n, MeasurableSet (U n))
    (hResidual : ∀ φ : BruhatCompactSupport C𝔽, (∀ g : C₁, φ.val g = 0) →
      Tendsto (fun n ↦ orderZeroProjectiveGeometricTrace φ (hu n).le U -
        orderZeroProjectiveGeometricTrace φ (by norm_num : (0 : ℝ) ≤ 1 / 2) U) atTop (𝓝 0))
    (φ : BruhatCompactSupport C𝔽) (hφ : ∀ g : C₁, φ.val g = 0) {α : ℝ} (hα : 0 < α) :
    HasSum (fun z : {z : SectionCharacterPoint(τ) // 0 < ord(z) ∧ α ≤ offset(z)} ↦
      zeroTerm(φ, z.val)) 0 := by
  have hOffLine : IsEmpty {z : SectionCharacterPoint(τ) // 0 < ord(z) ∧ 0 < offset(z)} := by
    apply isEmpty_selectedHeckeZeros_of_hasSum τ hτ (fun s ↦ 0 < |s.re - 1 / 2|)
    intro ψ hψ
    obtain ⟨S, hSum, hLimit⟩ :=
      hasSum_offCriticalZeros_orderZeroProjectiveGeometricTrace_limit τ hτ u hu hlim U hU hBorel
        ψ (hψ 1)
    have hZero : S = 0 := tendsto_nhds_unique hLimit (hResidual ψ hψ)
    exact hZero ▸ hSum
  apply (hasSum_exteriorZeros_iff_isEmpty τ hτ α).mpr _ φ hφ
  exact ⟨fun z ↦ @IsEmpty.false _ hOffLine ⟨z.val, z.property.1, hα.trans_le z.property.2⟩⟩

end OrderZeroDiagonalComparison

end RiemannMasullo.Isolated
