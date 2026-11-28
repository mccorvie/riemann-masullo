module

public import RiemannMasullo.Ch11_ShellStructure.Sec2b_RatEmptyLevel
public import RiemannMasullo.AppA_AlgebraicNT.Sec3_PositiveHaarHalfDensity
public import RiemannMasullo.ForMathlib.Analysis.Fourier.PositiveRayCosine
public import RiemannMasullo.Ch12_TraceGeometric.Sec4_RealPWLevelClosure

/-! # Exact transport of the actual rational local level to the flat real level

The true quotient Haar and polar test geometry are used at order zero, no finite
places, and half twist. The map onto the existing even polar-free level has no
undetermined Haar factor. -/

public noncomputable section

open MeasureTheory Function Set Filter NumberField IsDedekindDomain
open scoped NNReal ENNReal NumberField.AdeleRing FourierTransform SchwartzMap

namespace RiemannMasullo.RatEmptyRealLevelBridge
open RatEmptyGenuineLevel RatEmptyMeasureCoordinate RatEmptyHaarHalfDensity FlatPolar

local notation "S₀" => (∅ : Finset (HeightOneSpectrum (𝓞 ℚ)))
local notation "J" => SIdeleQuotient ℚ S₀
local notation "N" => sIdeleQuotientNorm ℚ S₀
local notation "ν" => sLocalQuotientTamagawaMeasure ℚ S₀
local instance : MeasurableSpace J := borel _
local notation "rad(" g ")" => ((Units.val (N g) : ℝ≥0) : ℝ)
local notation "ν₀" => Measure.withDensity ν (fun g ↦ ENNReal.ofReal
  (intervalSobolevDensity 0 0 0 (Real.log rad(g))))
local notation "W" => Lp ℂ 2 ν₀
local notation "H" => Lp ℂ 2 (volume : Measure ℝ)
local notation "ray" => volume.restrict (Ioi (0 : ℝ))
local notation "k" => (((Real.sqrt 2)⁻¹ : ℝ) : ℂ)

/-- The Haar half-density removes the twist before the normalized even extension. -/
def rayChart : W ≃ₗᵢ[ℂ] Lp ℂ 2 ray := haarAmbient.symm.trans halfDensity

def embedding : W →ₗᵢ[ℂ] H := positiveRayEvenExtension.comp rayChart.toLinearIsometry

private def signs (f : 𝓢(ℝ, ℂ)) : 𝓢(ℝ, ℂ) :=
  f + SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (LinearIsometryEquiv.neg ℝ (E := ℝ)) f

private theorem signs_apply (f : 𝓢(ℝ, ℂ)) (x : ℝ) : signs f x = f x + f (-x) := rfl

private theorem signs_even (f : 𝓢(ℝ, ℂ)) (x : ℝ) : signs f (-x) = signs f x := by
  simp only [signs_apply, neg_neg, add_comm]

private theorem signs_fourier (f : 𝓢(ℝ, ℂ)) (x : ℝ) :
    (𝓕 (signs f) : 𝓢(ℝ, ℂ)) x = (𝓕 f : 𝓢(ℝ, ℂ)) x + (𝓕 f : 𝓢(ℝ, ℂ)) (-x) := by
  let R := LinearIsometryEquiv.neg ℝ (E := ℝ)
  let g := SchwartzMap.compCLMOfContinuousLinearEquiv ℂ R.toContinuousLinearEquiv f
  have hg : (𝓕 g : 𝓢(ℝ, ℂ)) x = (𝓕 f : 𝓢(ℝ, ℂ)) (-x) := by
    rw [SchwartzMap.fourier_coe, SchwartzMap.fourier_coe]
    exact Real.fourier_comp_linearIsometry R (⇑f) x
  change (𝓕 (f + g) : 𝓢(ℝ, ℂ)) x = _
  rw [FourierTransform.fourier_add, add_apply, hg]

private theorem fourier_origin (f : 𝓢(ℝ, ℂ)) : (𝓕 f : 𝓢(ℝ, ℂ)) 0 = ∫ x, f x := by
  rw [SchwartzMap.fourier_coe, Real.fourier_real_eq_integral_exp_smul]
  simp

private theorem signs_core {B : ℝ} {f : 𝓢(ℝ, ℂ)} (hf : RealPolarBand B f) :
    (signs f).toLp 2 volume ∈ realPWPolarFreeCore B := by
  obtain ⟨h0, hF, hband⟩ := hf
  refine ⟨signs f, rfl, signs_even f, ?_, by simp [signs_apply, h0], ?_⟩
  · rw [← SchwartzMap.fourier_coe]
    apply closure_minimal _ isClosed_Icc
    intro x hx
    by_contra hn
    have hn' : -x ∉ Icc (-B) B := fun h ↦ hn ⟨by linarith [h.2], by linarith [h.1]⟩
    exact hx (by rw [signs_fourier, image_eq_zero_of_notMem_tsupport (fun h ↦ hn (hband h)),
      image_eq_zero_of_notMem_tsupport (fun h ↦ hn' (hband h)), add_zero])
  · rw [← fourier_origin, signs_fourier, neg_zero, hF, add_zero]

private def rayTest (f : 𝓢(ℝ, ℂ)) : Lp ℂ 2 ray :=
  (((signs f).memLp 2 volume).restrict (Ioi 0)).toLp _

private theorem rayTest_ae (f : 𝓢(ℝ, ℂ)) : ⇑(rayTest f) =ᵐ[ray] signs f :=
  MemLp.coeFn_toLp _

private def actualTest (f : 𝓢(ℝ, ℂ)) : W := rayChart.symm (rayTest f)

private theorem actualTest_ae (f : 𝓢(ℝ, ℂ)) :
    (actualTest f : J → ℂ) =ᵐ[ν] fun g ↦ profile f rad(g) := by
  let u := halfDensity.symm (rayTest f)
  have hν : ae ν ≤ ae ν₀ := by rw [zero_measure]
  have hu : (actualTest f : J → ℂ) =ᵐ[ν] u ∘ normEquiv := hν (haarAmbient_apply u)
  have hr := rad_ae (P := fun r ↦ rayTest f r = signs f r) (rayTest_ae f)
  have hh : ∀ᵐ t ∂positiveRealHaar, u t = profile f (t.val : ℝ) := by
    filter_upwards [halfDensity_symm_apply_ae (rayTest f), hr] with t ht hs
    change halfDensity.symm (rayTest f) t = _
    rw [ht, hs, signs_apply, profile, ← Real.sqrt_eq_rpow]
  exact hu.trans (norm_preserving.quasiMeasurePreserving.ae hh)

private theorem embedding_actualTest (f : 𝓢(ℝ, ℂ)) :
    embedding (actualTest f) = k • (signs f).toLp 2 volume := by
  change positiveRayEvenExtension (rayChart (rayChart.symm (rayTest f))) = _
  rw [LinearIsometryEquiv.apply_symm_apply]
  apply Lp.ext
  filter_upwards [positiveRayEvenExtension_apply (rayTest f),
    positiveRay_ae_abs (rayTest_ae f), (signs f).coeFn_toLp 2 volume,
    Lp.coeFn_smul k ((signs f).toLp 2 volume)] with x hx hr hf hs
  have habs : signs f |x| = signs f x := by
    rcases le_total 0 x with h | h
    · rw [abs_of_nonneg h]
    · rw [abs_of_nonpos h, signs_even]
  apply hx.trans
  rw [hr, habs, hs]
  change k * signs f x = k * ((signs f).toLp 2 volume) x
  rw [hf]

/-- Two signs from the arithmetic profile, one inverse square root from extension. -/
private theorem even_generator_scale : k * (2 : ℂ) = (Real.sqrt 2 : ℂ) := by
  have h : (Real.sqrt 2)⁻¹ * 2 = Real.sqrt 2 := by
    have hn : Real.sqrt 2 ≠ 0 := (Real.sqrt_pos.2 (by norm_num)).ne'
    field_simp [hn]
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  exact_mod_cast h

private def actualCore (B : ℝ) : Set W :=
  {v | ∃ f : 𝓢(ℝ, ℂ), RealPolarBand B f ∧ (v : J → ℂ) =ᵐ[ν] fun g ↦ profile f rad(g)}

private theorem coreSpan (B : ℝ) :
    (Submodule.span ℂ (actualCore B)).map embedding.toLinearMap =
      Submodule.span ℂ (realPWPolarFreeCore B) := by
  apply le_antisymm
  · apply (Submodule.map_span_le embedding.toLinearMap (actualCore B) _).2
    rintro v ⟨f, hf, hv⟩
    have heq : v = actualTest f := Lp.ext ((withDensity_absolutelyContinuous _ _).ae_le
      (hv.trans (actualTest_ae f).symm))
    change embedding v ∈ _
    rw [heq, embedding_actualTest]
    exact Submodule.smul_mem _ _ (Submodule.subset_span (signs_core hf))
  · apply Submodule.span_le.mpr
    rintro _ ⟨f, rfl, he, hb, hz, hi⟩
    have hp : RealPolarBand B f := ⟨hz, (fourier_origin f).trans hi, by
      simpa only [SchwartzMap.fourier_coe] using hb⟩
    let M := (Submodule.span ℂ (actualCore B)).map embedding.toLinearMap
    have hmem : embedding (actualTest f) ∈ M := ⟨actualTest f,
      Submodule.subset_span (show actualTest f ∈ actualCore B from ⟨f, hp, actualTest_ae f⟩), rfl⟩
    have htwo : (signs f).toLp 2 volume = (2 : ℂ) • f.toLp 2 volume := by
      apply Lp.ext
      filter_upwards [(signs f).coeFn_toLp 2 volume, f.coeFn_toLp 2 volume,
        Lp.coeFn_smul (2 : ℂ) (f.toLp 2 volume)] with x hx hy hs
      rw [hx, signs_apply, he, hs]
      simp [hy, two_mul]
    rw [embedding_actualTest, htwo, smul_smul, even_generator_scale] at hmem
    have hn : (Real.sqrt 2 : ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.2 (by norm_num : (0 : ℝ) < 2)).ne'
    change f.toLp 2 volume ∈ M
    simpa only [smul_smul, inv_mul_cancel₀ hn, one_smul] using
      M.smul_mem (Real.sqrt 2 : ℂ)⁻¹ hmem

/-- The image is the whole flat level, not just a subspace of the even band. -/
theorem map_invariantLevel (ω : PontryaginDual (N).ker) {B : ℝ} (hB : 0 < B) :
    (sLocalInvariantPWSobolev (F := ℚ) (S := S₀) (s := 0) le_rfl
      (by norm_num : (0 : ℝ) < 1 / 2) ω B).map embedding.toLinearMap = realPWLevel B := by
  rw [invariant_level_eq, ← topologicalClosure_span_realPWPolarFreeCore hB, ← coreSpan B]
  let M := Submodule.span ℂ (actualCore B)
  apply SetLike.coe_injective
  change embedding '' closure (M : Set W) = closure (embedding '' (M : Set W))
  exact (embedding.isometry.isClosedEmbedding.closure_image_eq _).symm

end RiemannMasullo.RatEmptyRealLevelBridge
