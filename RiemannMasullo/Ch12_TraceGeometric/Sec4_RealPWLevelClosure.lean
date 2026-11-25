module

public import Mathlib.Analysis.Fourier.LpSpace
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.MeasureTheory.Group.Integral

/-! # The Paley–Wiener level of the rational real-place model is the band less one line

Paper: Definition 11.2.1.1, pp. 487–488, as used in Theorem 12.4.1.1, pp. 514–519.

Over `ℚ` with no finite place, at order zero, the level is the closure in `L²(ℝ)` of the
polar-free core: the even Schwartz functions `f` with Fourier transform supported in `[-Y, Y]`,
`f 0 = 0` and `∫ f = 0`. This file proves what that closure is.

* `topologicalClosure_span_realPWPolarFreeCore`: the closure of the span of the core is
  `realPWLevel Y`, the even functions of the band whose Fourier transform has integral zero
  over the band. That condition is `f 0 = 0` for a function of the band: it says that `f` is
  orthogonal to the reproducing kernel of the band at the origin.
* `exists_mem_realPWLevel_integral_ne_zero`: the level contains an even Schwartz function of
  the band, vanishing at the origin, whose integral is not zero. So the condition `∫ f = 0`
  does not survive the closure.

Hence the level is the even band less one line, and the projection onto it is the projection
onto the even band minus a rank-one projection. This is the description used on issue 7354 and
in `Sec4_RealPWLevelDefect`, `Sec4_RealPWLevelDiagonal` and `Sec4_RealPWLevelTrace`, where it is
stated in words.

The proof of the closure is by duality. A vector of the level orthogonal to the core has a
Fourier transform that is constant on `(0, Y)`, by the fundamental lemma of the calculus of
variations, hence constant on the band, hence zero since its integral over the band is zero.

The identification of this model with `sLocalInvariantPWSobolev` over `ℚ` with no finite place
is proved in `Sec4_RealPWLevelBridge`.

**Not formalized.** Order zero only: with a logarithmic weight the norm changes and the
statement has to be proved again.
-/

open MeasureTheory Real Set Filter Topology
open scoped FourierTransform ComplexConjugate InnerProductSpace SchwartzMap ContDiff ENNReal

@[expose] public noncomputable section

namespace RiemannMasullo

local notation "H" => Lp ℂ 2 (volume : Measure ℝ)

/-- The band `[-Y, Y]` has finite measure. -/
theorem volume_Icc_neg_self_ne_top (Y : ℝ) : volume (Icc (-Y) Y) ≠ ⊤ := by
  rw [Real.volume_Icc]
  exact ENNReal.ofReal_ne_top

/-- The indicator of the band `[-Y, Y]` as a vector of `L²`. -/
def realBandIndicator (Y : ℝ) : H :=
  indicatorConstLp 2 (measurableSet_Icc : MeasurableSet (Icc (-Y) Y)) (volume_Icc_neg_self_ne_top Y)
    (1 : ℂ)

/-- The reflection `f ↦ f (-x)` on `L²`. -/
def realReflection : H →ₗᵢ[ℂ] H :=
  Lp.compMeasurePreservingₗᵢ ℂ (fun x : ℝ ↦ -x) (Measure.measurePreserving_neg volume)

/-- The frequency side of the level: square-integrable functions that vanish outside
`[-Y, Y]`, are even, and have integral zero over the band. -/
def realPWLevelFourier (Y : ℝ) : Submodule ℂ H :=
  LinearMap.ker (LpToLpRestrictCLM ℝ ℂ ℂ volume 2 (Icc (-Y) Y)ᶜ).toLinearMap ⊓
    LinearMap.ker (realReflection.toLinearMap - LinearMap.id) ⊓
    LinearMap.ker (innerSL ℂ (realBandIndicator Y)).toLinearMap

/-- Membership in the frequency side of the level, in terms of the function. -/
theorem mem_realPWLevelFourier_iff {Y : ℝ} {Ψ : H} : Ψ ∈ realPWLevelFourier Y ↔
    (∀ᵐ ξ, ξ ∉ Icc (-Y) Y → Ψ ξ = 0) ∧ (∀ᵐ ξ, Ψ (-ξ) = Ψ ξ) ∧
      ∫ ξ in Icc (-Y) Y, Ψ ξ = 0 := by
  simp only [realPWLevelFourier, Submodule.mem_inf, LinearMap.mem_ker, and_assoc,
    ContinuousLinearMap.coe_coe]
  refine and_congr ?_ (and_congr ?_ ?_)
  · have hco := LpToLpRestrictCLM_coeFn (𝕜 := ℂ) (Icc (-Y) Y)ᶜ Ψ
    have hae : (∀ᵐ ξ, ξ ∉ Icc (-Y) Y → Ψ ξ = 0) ↔
        ∀ᵐ ξ ∂volume.restrict (Icc (-Y) Y)ᶜ, Ψ ξ = 0 :=
      (ae_restrict_iff' (measurableSet_Icc.compl : MeasurableSet (Icc (-Y) Y)ᶜ)).symm
    rw [hae]
    constructor
    · intro h
      have h0 : (LpToLpRestrictCLM ℝ ℂ ℂ volume 2 (Icc (-Y) Y)ᶜ Ψ : ℝ → ℂ)
          =ᵐ[volume.restrict (Icc (-Y) Y)ᶜ] 0 := by
        have := (Lp.eq_zero_iff_ae_eq_zero
          (f := LpToLpRestrictCLM ℝ ℂ ℂ volume 2 (Icc (-Y) Y)ᶜ Ψ)).mp h
        exact this
      filter_upwards [hco, h0] with ξ h1 h2
      rw [← h1, h2]
      rfl
    · intro h
      refine (Lp.eq_zero_iff_ae_eq_zero).mpr ?_
      filter_upwards [hco, h] with ξ h1 h2
      rw [h1, h2]
      rfl
  · have hco := Lp.coeFn_compMeasurePreserving Ψ (Measure.measurePreserving_neg volume)
    simp only [LinearMap.sub_apply, LinearMap.id_coe, id_eq, sub_eq_zero]
    constructor
    · intro h
      have h' : (realReflection Ψ : ℝ → ℂ) =ᵐ[volume] Ψ := by
        have : realReflection Ψ = Ψ := h
        rw [this]
      filter_upwards [hco, h'] with ξ h1 h2
      rw [← h2]
      exact h1.symm ▸ rfl
    · intro h
      refine Lp.ext ?_
      filter_upwards [hco, h] with ξ h1 h2
      exact h1.trans h2
  · show inner ℂ (realBandIndicator Y) Ψ = 0 ↔ _
    rw [realBandIndicator, L2.inner_indicatorConstLp_one]

/-- Paper: Definition 11.2.1.1, pp. 487–488. The level in the rational real-place model at
order zero: the functions of `L²(ℝ)` whose Fourier transform vanishes outside `[-Y, Y]`, is
even, and has integral zero over the band. The last condition says that the function is
orthogonal to the inverse Fourier transform of the indicator of the band, which is the
reproducing kernel of the band at the origin.
Reconstruction: `topologicalClosure_span_realPWPolarFreeCore` proves that this is the closure
of the polar-free core, which is how the paper defines the level. -/
def realPWLevel (Y : ℝ) : Submodule ℂ H :=
  (realPWLevelFourier Y).comap (Lp.fourierTransformₗᵢ ℝ ℂ).toLinearEquiv.toLinearMap

/-- A function is in the level when its Fourier transform is in the frequency side. -/
theorem mem_realPWLevel_iff {Y : ℝ} {F : H} :
    F ∈ realPWLevel Y ↔ (𝓕 F : H) ∈ realPWLevelFourier Y := Iff.rfl

/-- Paper: Definition 11.2.1.1, pp. 487–488. The polar-free core in the rational real-place
model: the classes in `L²(ℝ)` of the even Schwartz functions with Fourier transform supported
in `[-Y, Y]` that vanish at the origin and have integral zero.
Reconstruction: over `ℚ` with no finite place the units are `±1`, so the θ-functions of the
polar-free tests are the even parts of such functions. -/
def realPWPolarFreeCore (Y : ℝ) : Set H :=
  {F | ∃ f : 𝓢(ℝ, ℂ), f.toLp 2 = F ∧ (∀ x, f (-x) = f x) ∧
    tsupport (𝓕 (f : ℝ → ℂ)) ⊆ Icc (-Y) Y ∧ f 0 = 0 ∧ ∫ x, f x = 0}

/-- The Fourier integral of an even function is even. -/
theorem fourier_neg_of_even {f : ℝ → ℂ} (hf : ∀ x, f (-x) = f x) (ξ : ℝ) :
    𝓕 f (-ξ) = 𝓕 f ξ := by
  rw [← Real.fourierInv_eq_fourier_neg, Real.fourierInv_eq_fourier_comp_neg,
    show (fun x ↦ f (-x)) = f from funext hf]

/-- The integral of the Fourier transform of a Schwartz function is its value at the origin. -/
theorem integral_fourier_schwartz (f : 𝓢(ℝ, ℂ)) : ∫ ξ, 𝓕 (f : ℝ → ℂ) ξ = f 0 := by
  have h : (𝓕⁻ (𝓕 f) : 𝓢(ℝ, ℂ)) = f := by simp
  have h0 : (𝓕⁻ (𝓕 f) : 𝓢(ℝ, ℂ)) 0 = f 0 := by rw [h]
  rw [← h0, SchwartzMap.fourierInv_coe, Real.fourierInv_eq_fourier_neg, neg_zero,
    Real.fourier_real_eq_integral_exp_smul, SchwartzMap.fourier_coe]
  simp

/-- An even Schwartz function with Fourier transform supported in `[-Y, Y]` that vanishes at the
origin is in the level. Its integral is not constrained. -/
theorem toLp_mem_realPWLevel {Y : ℝ} (f : 𝓢(ℝ, ℂ)) (heven : ∀ x, f (-x) = f x)
    (hsupp : tsupport (𝓕 (f : ℝ → ℂ)) ⊆ Icc (-Y) Y) (h0 : f 0 = 0) :
    (f.toLp 2 volume : H) ∈ realPWLevel Y := by
  rw [mem_realPWLevel_iff, SchwartzMap.toLp_fourier_eq, mem_realPWLevelFourier_iff]
  have hco : ((𝓕 f).toLp 2 : ℝ → ℂ) =ᵐ[volume] 𝓕 (f : ℝ → ℂ) := by
    have := (𝓕 f).coeFn_toLp 2 (μ := volume)
    rwa [SchwartzMap.fourier_coe] at this
  have hzero : ∀ ξ, ξ ∉ Icc (-Y) Y → 𝓕 (f : ℝ → ℂ) ξ = 0 := fun ξ hξ ↦
    image_eq_zero_of_notMem_tsupport fun hmem ↦ hξ (hsupp hmem)
  refine ⟨?_, ?_, ?_⟩
  · filter_upwards [hco] with ξ h hξ
    rw [h]
    exact hzero ξ hξ
  · have hneg :=
      (Measure.measurePreserving_neg (volume : Measure ℝ)).quasiMeasurePreserving.ae_eq_comp hco
    filter_upwards [hco, hneg] with ξ h1 h2
    have h3 : ((𝓕 f).toLp 2 : ℝ → ℂ) (-ξ) = 𝓕 (f : ℝ → ℂ) (-ξ) := h2
    rw [h1, h3]
    exact fourier_neg_of_even heven ξ
  · rw [setIntegral_congr_ae measurableSet_Icc (hco.mono fun ξ h _ ↦ h),
      setIntegral_eq_integral_of_forall_compl_eq_zero hzero, integral_fourier_schwartz, h0]

/-- The polar-free core lies in the level. -/
theorem realPWPolarFreeCore_subset (Y : ℝ) :
    realPWPolarFreeCore Y ⊆ (realPWLevel Y : Set H) := by
  rintro F ⟨f, rfl, heven, hsupp, h0, -⟩
  exact toLp_mem_realPWLevel f heven hsupp h0

/-- An even real smooth function with compact support is the Fourier transform of an even
Schwartz function, whose value at the origin is the integral of the function and whose integral
is the value of the function at the origin. -/
private theorem exists_schwartz_fourier_eq (G : ℝ → ℝ) (hG : ContDiff ℝ ∞ G)
    (hGc : HasCompactSupport G) (hGeven : ∀ ξ, G (-ξ) = G ξ) :
    ∃ f : 𝓢(ℝ, ℂ), (∀ ξ, 𝓕 (f : ℝ → ℂ) ξ = (G ξ : ℂ)) ∧ (∀ x, f (-x) = f x) ∧
      f 0 = ((∫ ξ, G ξ : ℝ) : ℂ) ∧ ∫ x, f x = (G 0 : ℂ) := by
  let GC : ℝ → ℂ := fun ξ ↦ (G ξ : ℂ)
  have hGs : ContDiff ℝ ∞ GC := Complex.ofRealCLM.contDiff.comp hG
  have hGCc : HasCompactSupport GC := hGc.comp_left Complex.ofReal_zero
  have hGCeven : ∀ ξ, GC (-ξ) = GC ξ := fun ξ ↦ by simp only [GC, hGeven]
  let Gs : 𝓢(ℝ, ℂ) := hGCc.toSchwartzMap hGs
  have hGs_coe : (Gs : ℝ → ℂ) = GC := rfl
  let f : 𝓢(ℝ, ℂ) := 𝓕⁻ Gs
  have hfG : (𝓕 f : 𝓢(ℝ, ℂ)) = Gs := by simp [f]
  have hfourier : ∀ ξ, 𝓕 (f : ℝ → ℂ) ξ = GC ξ := fun ξ ↦ by
    rw [← SchwartzMap.fourier_coe, hfG, hGs_coe]
  have hf_apply : ∀ x, f x = 𝓕 GC (-x) := fun x ↦ by
    change (𝓕⁻ Gs : 𝓢(ℝ, ℂ)) x = _
    rw [SchwartzMap.fourierInv_coe, Real.fourierInv_eq_fourier_neg, hGs_coe]
  refine ⟨f, hfourier, ?_, ?_, ?_⟩
  · intro x
    rw [hf_apply, hf_apply, neg_neg, fourier_neg_of_even hGCeven]
  · rw [hf_apply, neg_zero, Real.fourier_real_eq_integral_exp_smul, ← integral_complex_ofReal]
    simp [GC]
  · have h := Real.fourier_real_eq_integral_exp_smul (f : ℝ → ℂ) 0
    simp only [mul_zero, Complex.ofReal_zero, zero_mul, Complex.exp_zero, one_smul] at h
    rw [← h, hfourier]

/-- A real smooth function with compact support in `(0, Y)` and integral zero gives an element
of the core whose Fourier transform is the symmetrization of the function. -/
private theorem exists_core_of_smooth {Y : ℝ} (χ : ℝ → ℝ) (hχ : ContDiff ℝ ∞ χ)
    (hχc : HasCompactSupport χ) (hχs : tsupport χ ⊆ Ioo 0 Y) (hχ0 : ∫ ξ, χ ξ = 0) :
    ∃ f : 𝓢(ℝ, ℂ), (f.toLp 2 volume : H) ∈ realPWPolarFreeCore Y ∧
      ∀ ξ, 𝓕 (f : ℝ → ℂ) ξ = ((χ ξ + χ (-ξ) : ℝ) : ℂ) := by
  have hχ_zero : ∀ ξ, ξ ∉ Ioo (0 : ℝ) Y → χ ξ = 0 := fun ξ hξ ↦
    image_eq_zero_of_notMem_tsupport fun h ↦ hξ (hχs h)
  obtain ⟨f, hfourier, hfeven, hf0, hfint⟩ := exists_schwartz_fourier_eq
    (fun ξ ↦ χ ξ + χ (-ξ)) (hχ.add (hχ.comp contDiff_neg))
    (hχc.add (hχc.comp_homeomorph (Homeomorph.neg ℝ)))
    (fun ξ ↦ by simp only [neg_neg, add_comm])
  refine ⟨f, ⟨f, rfl, hfeven, ?_, ?_, ?_⟩, hfourier⟩
  · have hsub : Function.support (𝓕 (f : ℝ → ℂ)) ⊆ Icc (-Y) Y := by
      intro ξ hξ
      rw [Function.mem_support, hfourier] at hξ
      by_contra hmem
      apply hξ
      have h1 : χ ξ = 0 := hχ_zero ξ fun h ↦ hmem ⟨by linarith [h.1, h.2], h.2.le⟩
      have h2 : χ (-ξ) = 0 := hχ_zero (-ξ) fun h ↦
        hmem ⟨by linarith [h.1, h.2], by linarith [h.1, h.2]⟩
      simp [h1, h2]
    exact closure_minimal hsub isClosed_Icc
  · have h1 : Integrable χ := hχ.continuous.integrable_of_hasCompactSupport hχc
    have h2 : Integrable fun ξ ↦ χ (-ξ) := h1.comp_neg
    rw [hf0, integral_add h1 h2, integral_neg_eq_self χ volume, hχ0]
    simp
  · have h0 : χ 0 = 0 := hχ_zero 0 fun h ↦ lt_irrefl _ h.1
    rw [hfint]
    simp [h0]

private theorem inner_toLp_eq_integral (f : 𝓢(ℝ, ℂ)) (F : H) :
    ⟪(f.toLp 2 volume : H), F⟫_ℂ = ∫ ξ, conj (𝓕 (f : ℝ → ℂ) ξ) * (𝓕 F : H) ξ := by
  rw [← Lp.inner_fourier_eq, SchwartzMap.toLp_fourier_eq, L2.inner_def]
  refine integral_congr_ae ?_
  have hco := (𝓕 f).coeFn_toLp 2 (μ := volume)
  filter_upwards [hco] with ξ h
  rw [h, SchwartzMap.fourier_coe, RCLike.inner_apply, mul_comm]

private theorem eq_zero_of_orthogonal_core {Y : ℝ} (hY : 0 < Y) {F : H}
    (hF : F ∈ realPWLevel Y) (horth : ∀ c ∈ realPWPolarFreeCore Y, ⟪c, F⟫_ℂ = 0) : F = 0 := by
  obtain ⟨hout, heven, hint⟩ := mem_realPWLevelFourier_iff.mp (mem_realPWLevel_iff.mp hF)
  generalize hΨ : (𝓕 F : H) = Ψ at hout heven hint
  have hΨloc : LocallyIntegrable (Ψ : ℝ → ℂ) := (Lp.memLp Ψ).locallyIntegrable one_le_two
  let ψ : ContDiffBump (Y / 2 : ℝ) := ⟨Y / 8, Y / 4, by positivity, by linarith⟩
  have hψs : tsupport (ψ : ℝ → ℝ) ⊆ Ioo 0 Y := by
    rw [ψ.tsupport_eq, Real.closedBall_eq_Icc]
    intro ξ hξ
    have h1 : Y / 2 - Y / 4 ≤ ξ := hξ.1
    have h2 : ξ ≤ Y / 2 + Y / 4 := hξ.2
    exact ⟨by linarith, by linarith⟩
  have hψint : 0 < ∫ ξ, ψ ξ := ψ.integral_pos
  have key : ∀ χ : ℝ → ℝ, ContDiff ℝ ∞ χ → HasCompactSupport χ → tsupport χ ⊆ Ioo 0 Y →
      ∫ ξ, χ ξ = 0 → ∫ ξ, χ ξ • Ψ ξ = 0 := by
    intro χ hχ hχc hχs hχ0
    obtain ⟨f, hfc, hff⟩ := exists_core_of_smooth χ hχ hχc hχs hχ0
    have h := horth _ hfc
    rw [inner_toLp_eq_integral, hΨ] at h
    have h1 : Integrable fun ξ ↦ χ ξ • Ψ ξ :=
      hΨloc.integrable_smul_left_of_hasCompactSupport hχ.continuous hχc
    have h2 : Integrable fun ξ ↦ χ (-ξ) • Ψ ξ :=
      hΨloc.integrable_smul_left_of_hasCompactSupport (hχ.continuous.comp continuous_neg)
        (hχc.comp_homeomorph (Homeomorph.neg ℝ))
    have hsplit : ∫ ξ, conj (𝓕 (f : ℝ → ℂ) ξ) * Ψ ξ =
        (∫ ξ, χ ξ • Ψ ξ) + ∫ ξ, χ (-ξ) • Ψ ξ := by
      rw [← integral_add h1 h2]
      refine integral_congr_ae (Eventually.of_forall fun ξ ↦ ?_)
      simp only [hff, Complex.conj_ofReal, Complex.real_smul]
      push_cast
      ring
    have hrefl : ∫ ξ, χ (-ξ) • Ψ ξ = ∫ ξ, χ ξ • Ψ ξ := by
      rw [← integral_neg_eq_self (fun ξ ↦ χ ξ • Ψ ξ) volume]
      refine integral_congr_ae ?_
      filter_upwards [heven] with ξ hξ
      simp only [hξ]
    rw [hsplit, hrefl] at h
    have h2' : (2 : ℂ) * ∫ ξ, χ ξ • Ψ ξ = 0 := by
      rw [two_mul]
      exact h
    exact (mul_eq_zero.mp h2').resolve_left two_ne_zero
  set κ : ℂ := (∫ ξ, ψ ξ • Ψ ξ) / ((∫ ξ, ψ ξ : ℝ) : ℂ) with hκ
  have hne : ((∫ ξ, ψ ξ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hψint.ne'
  have hconst : ∀ᵐ ξ, ξ ∈ Ioo (0 : ℝ) Y → Ψ ξ - κ = 0 := by
    refine isOpen_Ioo.ae_eq_zero_of_integral_contDiff_smul_eq_zero ?_ ?_
    · exact (hΨloc.sub (locallyIntegrable_const κ)).locallyIntegrableOn _
    · intro g hg hgc hgs
      have hgi : Integrable g := hg.continuous.integrable_of_hasCompactSupport hgc
      have hψi : Integrable (ψ : ℝ → ℝ) := ψ.integrable
      set t : ℝ := (∫ ξ, g ξ) / ∫ ξ, ψ ξ with ht
      have hχ : ContDiff ℝ ∞ (fun ξ ↦ g ξ - t * ψ ξ) := hg.sub (contDiff_const.mul ψ.contDiff)
      have hχsupp : Function.support (fun ξ ↦ g ξ - t * ψ ξ) ⊆ tsupport g ∪ tsupport ψ := by
        intro ξ hξ
        by_contra hmem
        rw [mem_union, not_or] at hmem
        apply hξ
        simp [image_eq_zero_of_notMem_tsupport hmem.1, image_eq_zero_of_notMem_tsupport hmem.2]
      have hχts : tsupport (fun ξ ↦ g ξ - t * ψ ξ) ⊆ tsupport g ∪ tsupport ψ :=
        closure_minimal hχsupp ((isClosed_tsupport g).union (isClosed_tsupport ψ))
      have hχc : HasCompactSupport (fun ξ ↦ g ξ - t * ψ ξ) :=
        (hgc.isCompact.union ψ.hasCompactSupport.isCompact).of_isClosed_subset
          (isClosed_tsupport _) hχts
      have hχs : tsupport (fun ξ ↦ g ξ - t * ψ ξ) ⊆ Ioo 0 Y :=
        hχts.trans (union_subset hgs hψs)
      have hχ0 : ∫ ξ, (g ξ - t * ψ ξ) = 0 := by
        rw [integral_sub hgi (hψi.const_mul t), integral_const_mul, ht,
          div_mul_cancel₀ _ hψint.ne', sub_self]
      have hk := key _ hχ hχc hχs hχ0
      have h1 : Integrable fun ξ ↦ g ξ • Ψ ξ :=
        hΨloc.integrable_smul_left_of_hasCompactSupport hg.continuous hgc
      have h2 : Integrable fun ξ ↦ ψ ξ • Ψ ξ :=
        hΨloc.integrable_smul_left_of_hasCompactSupport ψ.continuous ψ.hasCompactSupport
      have e1 : ∫ ξ, (g ξ - t * ψ ξ) • Ψ ξ =
          (∫ ξ, g ξ • Ψ ξ) - (t : ℂ) * ∫ ξ, ψ ξ • Ψ ξ := by
        rw [← integral_const_mul, ← integral_sub h1 (h2.const_mul _)]
        refine integral_congr_ae (Eventually.of_forall fun ξ ↦ ?_)
        simp only [Complex.real_smul]
        push_cast
        ring
      have h3 : Integrable fun ξ ↦ g ξ • κ := hgi.smul_const κ
      have e2 : ∫ ξ, g ξ • (Ψ ξ - κ) = (∫ ξ, g ξ • Ψ ξ) - ((∫ ξ, g ξ : ℝ) : ℂ) * κ := by
        rw [show (fun ξ ↦ g ξ • (Ψ ξ - κ)) = fun ξ ↦ g ξ • Ψ ξ - g ξ • κ from
          funext fun ξ ↦ smul_sub _ _ _, integral_sub h1 h3, integral_smul_const,
          Complex.real_smul]
      rw [e2]
      rw [e1] at hk
      have hcomb : ((∫ ξ, g ξ : ℝ) : ℂ) * κ = (t : ℂ) * ∫ ξ, ψ ξ • Ψ ξ := by
        rw [hκ, ht]
        push_cast
        field_simp
      rw [hcomb]
      exact hk
  have hconst' : ∀ᵐ ξ, ξ ∈ Ioo (-Y) 0 → Ψ ξ - κ = 0 := by
    have hneg :=
      (Measure.measurePreserving_neg (volume : Measure ℝ)).quasiMeasurePreserving.ae hconst
    filter_upwards [hneg, heven] with ξ h1 h2 hξ
    rw [← h2]
    exact h1 ⟨by linarith [hξ.2], by linarith [hξ.1]⟩
  have hnull : ∀ᵐ ξ : ℝ, ξ ≠ 0 ∧ ξ ≠ Y ∧ ξ ≠ -Y := by
    have h : ∀ a : ℝ, ∀ᵐ ξ : ℝ, ξ ≠ a := fun a ↦ by
      rw [ae_iff]
      simp
    filter_upwards [h 0, h Y, h (-Y)] with ξ h1 h2 h3 using ⟨h1, h2, h3⟩
  have hIcc : ∀ᵐ ξ, ξ ∈ Icc (-Y) Y → Ψ ξ = κ := by
    filter_upwards [hconst, hconst', hnull] with ξ h1 h2 h3 hξ
    rcases lt_trichotomy ξ 0 with h | h | h
    · exact sub_eq_zero.mp (h2 ⟨lt_of_le_of_ne hξ.1 (Ne.symm h3.2.2), h⟩)
    · exact absurd h h3.1
    · exact sub_eq_zero.mp (h1 ⟨h, lt_of_le_of_ne hξ.2 h3.2.1⟩)
  have hκ0 : κ = 0 := by
    have h : ∫ ξ in Icc (-Y) Y, Ψ ξ = ∫ ξ in Icc (-Y) Y, κ :=
      setIntegral_congr_ae measurableSet_Icc hIcc
    rw [hint, setIntegral_const] at h
    have hv : volume.real (Icc (-Y) Y) = 2 * Y := by
      rw [Measure.real, Real.volume_Icc, ENNReal.toReal_ofReal (by linarith)]
      ring
    rw [hv, Complex.real_smul] at h
    have h2Y : ((2 * Y : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (by positivity : (2 * Y : ℝ) ≠ 0)
    exact ((mul_eq_zero.mp h.symm).resolve_left h2Y)
  have hΨ0 : Ψ = 0 := by
    refine Lp.eq_zero_iff_ae_eq_zero.mpr ?_
    filter_upwards [hout, hIcc] with ξ h1 h2
    by_cases hξ : ξ ∈ Icc (-Y) Y
    · rw [h2 hξ, hκ0]
      rfl
    · rw [h1 hξ]
      rfl
  rw [hΨ0] at hΨ
  exact (Lp.fourierTransformₗᵢ ℝ ℂ).map_eq_zero_iff.mp hΨ

/-- The frequency side of the level is closed. -/
theorem isClosed_realPWLevelFourier (Y : ℝ) : IsClosed (realPWLevelFourier Y : Set H) := by
  have h : (realPWLevelFourier Y : Set H) =
      ({Ψ | LpToLpRestrictCLM ℝ ℂ ℂ volume 2 (Icc (-Y) Y)ᶜ Ψ = 0} ∩
        {Ψ | realReflection Ψ = Ψ}) ∩ {Ψ | inner ℂ (realBandIndicator Y) Ψ = 0} := by
    ext Ψ
    simp only [realPWLevelFourier, Submodule.coe_inf, mem_inter_iff, SetLike.mem_coe,
      LinearMap.mem_ker, ContinuousLinearMap.coe_coe, LinearMap.sub_apply, LinearMap.id_coe,
      id_eq, sub_eq_zero, mem_ofPred_eq, LinearIsometry.coe_toLinearMap, innerSL_apply_apply]
  rw [h]
  exact ((isClosed_eq (ContinuousLinearMap.continuous _) continuous_const).inter
    (isClosed_eq realReflection.continuous continuous_id)).inter
    (isClosed_eq (continuous_const.inner continuous_id) continuous_const)

/-- The level is closed. -/
theorem isClosed_realPWLevel (Y : ℝ) : IsClosed (realPWLevel Y : Set H) :=
  (isClosed_realPWLevelFourier Y).preimage (Lp.fourierTransformₗᵢ ℝ ℂ).continuous

/-- Paper: Definition 11.2.1.1, pp. 487–488. **The level is the closure of the polar-free
core.** In `L²(ℝ)` the closure of the span of the polar-free core is the space of even functions
of the band that are orthogonal to the reproducing kernel of the band at the origin. Of the two
polar conditions only the vanishing at the origin survives the closure.
Reconstruction: the rational real-place model at order zero. -/
theorem topologicalClosure_span_realPWPolarFreeCore {Y : ℝ} (hY : 0 < Y) :
    (Submodule.span ℂ (realPWPolarFreeCore Y)).topologicalClosure = realPWLevel Y := by
  have hle : (Submodule.span ℂ (realPWPolarFreeCore Y)).topologicalClosure ≤ realPWLevel Y :=
    Submodule.topologicalClosure_minimal _
      (Submodule.span_le.mpr (realPWPolarFreeCore_subset Y)) (isClosed_realPWLevel Y)
  refine le_antisymm hle fun F hF ↦ ?_
  generalize hK : (Submodule.span ℂ (realPWPolarFreeCore Y)).topologicalClosure = K at hle ⊢
  have hKc : IsClosed (K : Set H) := hK ▸ Submodule.isClosed_topologicalClosure _
  have : CompleteSpace K := hKc.completeSpace_coe
  have hcore : ∀ c ∈ realPWPolarFreeCore Y, c ∈ K := fun c hc ↦
    hK ▸ Submodule.le_topologicalClosure _ (Submodule.subset_span hc)
  have hsub : F - K.starProjection F ∈ realPWLevel Y :=
    Submodule.sub_mem _ hF (hle (Submodule.starProjection_apply_mem K F))
  have horth : ∀ c ∈ realPWPolarFreeCore Y, ⟪c, F - K.starProjection F⟫_ℂ = 0 := fun c hc ↦
    (Submodule.mem_orthogonal K _).mp (Submodule.sub_starProjection_mem_orthogonal F) c
      (hcore c hc)
  have h0 := eq_zero_of_orthogonal_core hY hsub horth
  rw [sub_eq_zero] at h0
  rw [h0]
  exact Submodule.starProjection_apply_mem K F

/-- **The zero-integral condition does not survive the closure.** The level contains the class
of an even Schwartz function, with Fourier transform supported in `[-Y, Y]` and vanishing at the
origin, whose integral is not zero. -/
theorem exists_mem_realPWLevel_integral_ne_zero {Y : ℝ} (hY : 0 < Y) :
    ∃ f : 𝓢(ℝ, ℂ), (f.toLp 2 volume : H) ∈ realPWLevel Y ∧ ∫ x, f x ≠ 0 := by
  let ψ₀ : ContDiffBump (0 : ℝ) := ⟨Y / 16, Y / 8, by positivity, by linarith⟩
  let ψ : ContDiffBump (Y / 2 : ℝ) := ⟨Y / 8, Y / 4, by positivity, by linarith⟩
  have hψint : 0 < ∫ ξ, ψ ξ := ψ.integral_pos
  set t : ℝ := (∫ ξ, ψ₀ ξ) / (2 * ∫ ξ, ψ ξ) with ht
  let G : ℝ → ℝ := fun ξ ↦ ψ₀ ξ - t * (ψ ξ + ψ (-ξ))
  have hG : ContDiff ℝ ∞ G :=
    ψ₀.contDiff.sub (contDiff_const.mul (ψ.contDiff.add (ψ.contDiff.comp contDiff_neg)))
  have hψ₀zero : ∀ ξ : ℝ, Y / 8 ≤ |ξ| → ψ₀ ξ = 0 := fun ξ h ↦
    ψ₀.zero_of_le_dist (by rw [Real.dist_eq, sub_zero]; exact h)
  have hψzero : ∀ ξ : ℝ, Y / 4 ≤ |ξ - Y / 2| → ψ ξ = 0 := fun ξ h ↦
    ψ.zero_of_le_dist (by rw [Real.dist_eq]; exact h)
  have hGzero : ∀ ξ, ξ ∉ Icc (-Y) Y → G ξ = 0 := by
    intro ξ hξ
    rw [mem_Icc, not_and_or, not_le, not_le] at hξ
    have h1 : ψ₀ ξ = 0 := hψ₀zero ξ (by
      rcases hξ with h | h
      · exact (by linarith : Y / 8 ≤ -ξ).trans (neg_le_abs ξ)
      · exact (by linarith : Y / 8 ≤ ξ).trans (le_abs_self ξ))
    have h2 : ψ ξ = 0 := hψzero ξ (by
      rcases hξ with h | h
      · exact (by linarith : Y / 4 ≤ -(ξ - Y / 2)).trans (neg_le_abs _)
      · exact (by linarith : Y / 4 ≤ ξ - Y / 2).trans (le_abs_self _))
    have h3 : ψ (-ξ) = 0 := hψzero (-ξ) (by
      rcases hξ with h | h
      · exact (by linarith : Y / 4 ≤ -ξ - Y / 2).trans (le_abs_self _)
      · exact (by linarith : Y / 4 ≤ -(-ξ - Y / 2)).trans (neg_le_abs _))
    simp only [G, h1, h2, h3]
    ring
  have hGc : HasCompactSupport G := HasCompactSupport.intro isCompact_Icc hGzero
  have hGeven : ∀ ξ, G (-ξ) = G ξ := fun ξ ↦ by
    simp only [G, ψ₀.neg, neg_neg, add_comm]
  obtain ⟨f, hfourier, hfeven, hf0, hfint⟩ := exists_schwartz_fourier_eq G hG hGc hGeven
  refine ⟨f, toLp_mem_realPWLevel f hfeven ?_ ?_, ?_⟩
  · have hsub : Function.support (𝓕 (f : ℝ → ℂ)) ⊆ Icc (-Y) Y := by
      intro ξ hξ
      rw [Function.mem_support, hfourier] at hξ
      by_contra hmem
      exact hξ (by rw [hGzero ξ hmem, Complex.ofReal_zero])
    exact closure_minimal hsub isClosed_Icc
  · have h0 : Integrable (ψ₀ : ℝ → ℝ) := ψ₀.integrable
    have h1 : Integrable (ψ : ℝ → ℝ) := ψ.integrable
    have h2 : Integrable fun ξ ↦ ψ (-ξ) := h1.comp_neg
    have hint : ∫ ξ, G ξ = 0 := by
      have h12 : Integrable fun ξ ↦ t * (ψ ξ + ψ (-ξ)) := (h1.add h2).const_mul t
      have hadd : ∫ ξ, (ψ ξ + ψ (-ξ)) = (∫ ξ, ψ ξ) + ∫ ξ, ψ (-ξ) := integral_add h1 h2
      simp only [G]
      rw [integral_sub h0 h12, integral_const_mul, hadd,
        integral_neg_eq_self (ψ : ℝ → ℝ) volume, ht]
      field_simp
      ring
    rw [hf0, hint, Complex.ofReal_zero]
  · rw [hfint]
    have h1 : ψ₀ 0 = 1 := ψ₀.one_of_mem_closedBall (Metric.mem_closedBall_self (by positivity))
    have h2 : ψ 0 = 0 := hψzero 0 (by
      rw [zero_sub, abs_neg, abs_of_pos (by positivity : (0 : ℝ) < Y / 2)]
      linarith)
    have hG0 : G 0 = 1 := by simp only [G, h1, neg_zero, h2]; ring
    rw [hG0]
    norm_num

end RiemannMasullo
