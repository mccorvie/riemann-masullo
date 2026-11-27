module

public import RiemannMasullo.Ch01_Introduction.Sec4_HeckeGreenHeightTail
import Mathlib.Geometry.Manifold.PartitionOfUnity
import RiemannMasullo.Ch10_TraceSpectral.Sec4b_ProjectedKernels
public import RiemannMasullo.Ch12_TraceGeometric.Sec5

public import RiemannMasullo.Ch01_Introduction.Sec4_PoissonCertificate
public import RiemannMasullo.Ch01_Introduction.Sec4_HeckeGreenExterior
public import RiemannMasullo.AppB_AnalyticNT.Sec4b_BoundaryHeckeGreen

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

/-- Paper: Theorem 12.5.1.1, pp. 519–520.
Reconstruction: If all positive divisor points through height
`H` are central, an upper bound for the full two-sided quadratic tail gives a bound
for the corrected logarithmic integral on the critical line. -/
theorem criticalLogDifference_mem_Icc_of_verified_height (τ : ℝ≥0ˣ →ₜ* C𝔽)
    (hτ : Function.RightInverse τ (ideleClassNorm F)) (χ : U𝔽) (hχ : ∀ u : ℝ≥0ˣ, χ (τ u) = 1)
    {H B : ℝ} (hH : 0 < H) (hc : ∀ z : Site χ, |z.val.im| ≤ H → z.val.re = 1 / 2)
    (hB : inverseHeightTail χ H 2 ≤ B) :
    criticalLogDifference χ ∈ Icc 0 (3 / 4 * B) := by
  rw [criticalLogDifference_eq_mass τ hτ χ hχ]
  exact ⟨rightGreenMass_nonneg χ, (rightGreenMass_le_inverseHeightTail χ hH hc).trans
    (mul_le_mul_of_nonneg_left hB (by norm_num))⟩

/-- Paper: Theorem 12.5.1.1, pp. 519–520.
Reconstruction: For each compact test, character and `k ≥ 2`,
one Mellin envelope times the full high-ordinate tail bounds the absolute omitted sum.
The estimate holds at every positive strip half-width and includes both edges. -/
theorem exists_hasSum_absolute_exterior_le_verified_height_tail (χ : U𝔽)
    (φ : BruhatCompactSupport C𝔽) {k : ℕ} (hk : 2 ≤ k) :
    ∃ W : ℝ, 0 ≤ W ∧ ∀ {H B : ℝ}, 0 < H →
      (∀ z : Site χ, |z.val.im| ≤ H → z.val.re = 1 / 2) → inverseHeightTail χ H k ≤ B →
      ∀ α : ℝ, 0 < α → ∃ A : ℝ,
        HasSum (fun z : {p : ℂ // 0 < ord(χ, p) ∧ α ≤ |p.re - 1 / 2|} ↦
          ‖(ord(χ, z.val) : ℂ) * modulatedFourierMellin m𝔽 univ
            ⟨isProperMap_ideleClassNorm F, ideleClassNorm_ne_one (F := F)⟩
            μ𝔽 φ.val (ideleClassNormTwist χ (z.val - 1 / 2))‖) A ∧ A ≤ W * B := by
  obtain ⟨W, hW, hM⟩ := exists_centeredMellin_site_pow_envelope φ χ k
  refine ⟨W, hW, fun {H B} hH hc hB α hα ↦ ?_⟩
  let M (z : ℂ) := modulatedFourierMellin m𝔽 univ
    ⟨isProperMap_ideleClassNorm F, ideleClassNorm_ne_one (F := F)⟩
    μ𝔽 φ.val (ideleClassNormTwist χ (z - 1 / 2))
  obtain ⟨hs, hb⟩ := absolute_exterior_le_inverseHeightTail χ M hk hH hW hc hM hα
  exact ⟨_, hs, hb.trans (mul_le_mul_of_nonneg_left hB hW)⟩

/-- Paper: Theorem 12.5.1.1, pp. 519–520.
Reconstruction: A summable family of characterwise height-tail bounds controls the absolute
exterior sum on the original joint index.
The test envelopes are chosen before the verification heights and strip width. -/
theorem exists_hasSum_joint_absolute_exterior_le_verified_height_tails
    (τ : ℝ≥0ˣ →ₜ* C𝔽) (φ : BruhatCompactSupport C𝔽) {k : ℕ} (hk : 2 ≤ k) :
    let X := {χ : U𝔽 // ∀ u : ℝ≥0ˣ, χ (τ u) = 1}
    let M (χ : X) (s : ℂ) := modulatedFourierMellin m𝔽 univ
      ⟨isProperMap_ideleClassNorm F, ideleClassNorm_ne_one (F := F)⟩
      μ𝔽 φ.val (ideleClassNormTwist χ.val (s - 1 / 2))
    ∃ W : X → ℝ, (∀ χ, 0 ≤ W χ) ∧
      (∀ χ (z : Site χ.val), |z.val.im| ^ k * ‖M χ z.val‖ ≤ W χ) ∧
      ∀ H B : X → ℝ, (∀ χ, 0 < H χ) →
        (∀ χ (z : Site χ.val), |z.val.im| ≤ H χ → z.val.re = 1 / 2) →
        (∀ χ, inverseHeightTail χ.val (H χ) k ≤ B χ) →
        Summable (fun χ ↦ W χ * B χ) → ∀ α : ℝ, 0 < α → ∃ A : ℝ,
          HasSum (fun z : ext(τ, α) ↦ ‖(ord(z.val.1.val, z.val.2) : ℂ) * M z.val.1 z.val.2‖) A ∧
            A ≤ ∑' χ, W χ * B χ := by
  intro X M
  choose W hW hm using fun χ : X ↦ exists_centeredMellin_site_pow_envelope φ χ.val k
  refine ⟨W, hW, hm, fun H B hH hc hB hsum α hα ↦ ?_⟩
  let P (χ : X) (z : ℂ) := 0 < ord(χ.val, z) ∧ α ≤ |z.re - 1 / 2|
  let g (χ : X) (z : Subtype (P χ)) := ‖(ord(χ.val, z.val) : ℂ) * M χ z.val‖
  have hf (χ : X) : Summable (g χ) ∧ (∑' z, g χ z) ≤ W χ * B χ := by
    obtain ⟨hs, hb⟩ := absolute_exterior_le_inverseHeightTail χ.val (M χ) hk
      (hH χ) (hW χ) (hc χ) (hm χ) hα
    exact ⟨hs.summable, hb.trans (mul_le_mul_of_nonneg_left (hB χ) (hW χ))⟩
  have hout : Summable (fun χ ↦ ∑' z, g χ z) := Summable.of_nonneg_of_le
    (fun χ ↦ tsum_nonneg fun _ ↦ norm_nonneg _) (fun χ ↦ (hf χ).2) hsum
  have hσ : Summable (fun z : (χ : X) × Subtype (P χ) ↦ g z.1 z.2) :=
    (summable_sigma_of_nonneg fun _ ↦ norm_nonneg _).2 ⟨fun χ ↦ (hf χ).1, hout⟩
  refine ⟨_, ?_, hout.tsum_le_tsum (fun χ ↦ (hf χ).2) hsum⟩
  exact (Equiv.subtypeProdEquivSigmaSubtype P).symm.hasSum_iff.mp
    (hout.hasSum.sigma_of_hasSum (fun χ ↦ (hf χ).1.hasSum) hσ)

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

end CompactGreen

end RiemannMasullo.Isolated
