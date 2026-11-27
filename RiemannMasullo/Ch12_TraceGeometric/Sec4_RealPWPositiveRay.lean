module

public import RiemannMasullo.Ch12_TraceGeometric.Sec4_FlatPhysicalDilation
public import RiemannMasullo.Ch12_TraceGeometric.Sec4_RealPWLevelClosure

/-!
# The normalized even extension identifies the two order-zero real Paley–Wiener levels

The image of the physical positive-ray mean-zero band under normalized even
extension is exactly the independently defined full-line real Paley–Wiener
level. The full-line projection on even functions is the extension of the
physical orthogonal projection.
-/

open Filter Function MeasureTheory Set
open scoped FourierTransform ComplexConjugate ComplexInnerProductSpace

@[expose] public noncomputable section

namespace RiemannMasullo.FlatPolar

local notation "ν₊" => volume.restrict (Ioi (0 : ℝ))
local notation "H₊" => Lp ℂ 2 ν₊
local notation "Hℝ" => Lp ℂ 2 (volume : Measure ℝ)
local notation "J₊" => positiveRayEvenExtension
local notation "C₊" => positiveRayInverseCosineEquiv

/-- The normalized positive-ray extension is even almost everywhere on the full line. -/
theorem positiveRayEvenExtension_ae_even (f : H₊) :
    ∀ᵐ x ∂volume, J₊ f (-x) = J₊ f x := by
  have h := positiveRayEvenExtension_apply f
  filter_upwards [h, (Measure.measurePreserving_neg (volume : Measure ℝ)).quasiMeasurePreserving.ae_eq_comp h]
    with x hp hn
  change J₊ f (-x) = (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) * f |-x| at hn
  rw [hn, abs_neg, hp]

/-- At the named normalized polar vector the full-line extension is the band
indicator scaled by the product of the two normalization factors. -/
theorem positiveRayEvenExtension_bandVector_eq_realBandIndicator (B : ℝ) :
    J₊ (bandVector B) =
      ((((Real.sqrt 2)⁻¹ : ℝ) : ℂ) * (Real.sqrt B : ℂ)⁻¹) • realBandIndicator B := by
  let k := (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) * (Real.sqrt B : ℂ)⁻¹
  have hI : (realBandIndicator B : ℝ → ℂ) =ᵐ[volume] (Icc (-B) B).indicator (fun _ ↦ (1 : ℂ)) :=
    indicatorConstLp_coeFn
  apply Lp.ext
  filter_upwards [positiveRayEvenExtension_apply (bandVector B), positiveRay_ae_abs (bandVector_ae_eq B),
    (volume : Measure ℝ).ae_ne (0 : ℝ), Lp.coeFn_smul k (realBandIndicator B), hI] with x hJ hB hx hs hI
  have hpos : 0 < |x| := abs_pos.mpr hx
  have hin : |x| ∈ Ioc 0 B ↔ x ∈ Icc (-B) B := by
    simp only [mem_Ioc, mem_Icc, hpos, true_and, abs_le]
  change J₊ (bandVector B) x = (k • realBandIndicator B) x
  rw [hJ, hB, hs]
  change (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) * bandProfile B |x| = k * realBandIndicator B x
  rw [hI]
  by_cases hb : x ∈ Icc (-B) B
  · simp only [bandProfile, indicator_of_mem (hin.mpr hb), indicator_of_mem hb, mul_one, k]
  · simp only [bandProfile, indicator_of_notMem (fun h ↦ hb (hin.mp h)), indicator_of_notMem hb, mul_zero]

private theorem evenExtension_bandSupport_iff (B : ℝ) (f : H₊) :
    (∀ᵐ x ∂volume, x ∉ Icc (-B) B → J₊ f x = 0) ↔ f ∈ frequencyBand B := by
  rw [mem_frequencyBand_iff]
  constructor
  · intro hf
    filter_upwards [ae_restrict_mem (μ := (volume : Measure ℝ)) measurableSet_Ioi,
      ae_mono Measure.restrict_le_self hf,
      ae_mono (Measure.restrict_le_self (s := Ioi (0 : ℝ))) (positiveRayEvenExtension_apply f)]
      with x hpos hzero hrep
    intro hx
    have hout : x ∉ Icc (-B) B := fun h ↦ hx ⟨hpos, h.2⟩
    have hz := hzero hout
    rw [hrep, abs_of_pos hpos] at hz
    exact (mul_eq_zero.mp hz).resolve_left (Complex.ofReal_ne_zero.mpr (inv_ne_zero
      (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2)).ne'))
  · intro hf
    filter_upwards [positiveRay_ae_abs hf, positiveRayEvenExtension_apply f] with x hzero hrep
    intro hx
    have hout : |x| ∉ Ioc 0 B := fun h ↦ hx (abs_le.mp h.2)
    rw [hrep, hzero hout, mul_zero]

private theorem evenExtension_bandIntegral_zero_iff {B : ℝ} (hB : 0 < B) (f : H₊) :
    (∫ x in Icc (-B) B, J₊ f x) = 0 ↔ f ∈ (ℂ ∙ bandVector B)ᗮ := by
  rw [Submodule.mem_orthogonal_singleton_iff_inner_right]
  have hI : inner ℂ (realBandIndicator B) (J₊ f) = ∫ x in Icc (-B) B, J₊ f x := by
    rw [realBandIndicator, L2.inner_indicatorConstLp_one]
  rw [← hI]
  let k := (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) * (Real.sqrt B : ℂ)⁻¹
  have hk : k ≠ 0 := mul_ne_zero
    (Complex.ofReal_ne_zero.mpr (inv_ne_zero (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2)).ne'))
    (inv_ne_zero (Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hB).ne'))
  have h := J₊.inner_map_map (bandVector B) f
  rw [positiveRayEvenExtension_bandVector_eq_realBandIndicator, inner_smul_left] at h
  change (starRingEnd ℂ) k * inner ℂ (realBandIndicator B) (J₊ f) = inner ℂ (bandVector B) f at h
  rw [← h, mul_eq_zero]
  simp [hk]

/-- The full-line frequency conditions for a normalized even extension are
equivalent to membership of its ray input in the genuine mean-zero band. -/
theorem positiveRayEvenExtension_mem_realPWLevelFourier_iff {B : ℝ} (hB : 0 < B) (f : H₊) :
    J₊ f ∈ realPWLevelFourier B ↔ f ∈ meanZeroFrequencyBand B := by
  rw [mem_realPWLevelFourier_iff, evenExtension_bandSupport_iff,
    evenExtension_bandIntegral_zero_iff hB]
  change (_ ∧ _ ∧ _) ↔ (_ ∧ _)
  exact ⟨fun h ↦ ⟨h.1, h.2.2⟩, fun h ↦ ⟨h.1, positiveRayEvenExtension_ae_even f, h.2⟩⟩

/-- The full-line frequency submodule consists exactly of the normalized
even extensions of the positive-ray frequency band with mean zero. -/
theorem map_meanZeroFrequencyBand_positiveRayEvenExtension {B : ℝ} (hB : 0 < B) :
    (meanZeroFrequencyBand B).map J₊.toLinearMap = realPWLevelFourier B := by
  ext Ψ
  constructor
  · rintro ⟨f, hf, rfl⟩
    exact (positiveRayEvenExtension_mem_realPWLevelFourier_iff hB f).mpr hf
  · intro hΨ
    obtain ⟨f, he⟩ := mem_range_positiveRayEvenExtension_of_even Ψ ((mem_realPWLevelFourier_iff.mp hΨ).2.1)
    exact ⟨f, (positiveRayEvenExtension_mem_realPWLevelFourier_iff hB f).mp (he.symm ▸ hΨ), he⟩

/-- The cosine image of the positive-ray mean-zero band, then normalized even
extension, is precisely the full-line zero-order Paley–Wiener level. -/
theorem map_physicalMeanZeroBand_positiveRayEvenExtension {B : ℝ} (hB : 0 < B) :
    ((meanZeroFrequencyBand B).map (C₊.toLinearEquiv : H₊ →ₗ[ℂ] H₊)).map J₊.toLinearMap =
      realPWLevel B := by
  ext F
  constructor
  · rintro ⟨_, ⟨f, hf, rfl⟩, rfl⟩
    rw [mem_realPWLevel_iff]
    change 𝓕 (J₊ (positiveRayInverseCosine f)) ∈ realPWLevelFourier B
    rw [positiveRayInverseCosine_evenExtension, positiveRayInverseFourierEmbedding_apply,
      FourierTransform.fourier_fourierInv_eq]
    exact (positiveRayEvenExtension_mem_realPWLevelFourier_iff hB f).mpr hf
  · intro hF
    have hdata := mem_realPWLevel_iff.mp hF
    rw [← map_meanZeroFrequencyBand_positiveRayEvenExtension hB] at hdata
    obtain ⟨f, hf, he⟩ := hdata
    refine ⟨C₊ f, ⟨f, hf, rfl⟩, ?_⟩
    change J₊ f = 𝓕 F at he
    change J₊ (positiveRayInverseCosine f) = F
    rw [positiveRayInverseCosine_evenExtension, positiveRayInverseFourierEmbedding_apply, he,
      FourierTransform.fourierInv_fourier_eq]

/-- The normalized even extension of the physical subspace is exactly the closed
span of the full-line even Schwartz polar-free Paley–Wiener core. -/
theorem map_physicalMeanZeroBand_eq_closure_realPWPolarFreeCore {B : ℝ} (hB : 0 < B) :
    ((meanZeroFrequencyBand B).map (C₊.toLinearEquiv : H₊ →ₗ[ℂ] H₊)).map J₊.toLinearMap =
      (Submodule.span ℂ (realPWPolarFreeCore B)).topologicalClosure := by
  rw [map_physicalMeanZeroBand_positiveRayEvenExtension hB, topologicalClosure_span_realPWPolarFreeCore hB]

private theorem projection_evenExtension_of_map_eq (K : Submodule ℂ H₊) [K.HasOrthogonalProjection]
    (L : Submodule ℂ Hℝ) [L.HasOrthogonalProjection] (h : K.map J₊.toLinearMap = L) (f : H₊) :
    L.starProjection (J₊ f) = J₊ (K.starProjection f) := by
  subst L
  exact (J₊.map_starProjection K f).symm

/-- On every normalized even extension the independently defined full-line
orthogonal projection agrees with the positive-ray physical mean-zero projection. -/
theorem realPWLevel_starProjection_positiveRayEvenExtension {B : ℝ} (hB : 0 < B) (f : H₊) :
    letI : CompleteSpace (realPWLevel B) := (isClosed_realPWLevel B).completeSpace_coe
    (realPWLevel B).starProjection (J₊ f) = J₊ (physicalMeanZeroBandProjection B f) := by
  let : CompleteSpace (realPWLevel B) := (isClosed_realPWLevel B).completeSpace_coe
  exact projection_evenExtension_of_map_eq _ _ (map_physicalMeanZeroBand_positiveRayEvenExtension hB) f

/-- On the full Hilbert space the projection is the ray physical projection
between the normalized even extension and its Hilbert adjoint. -/
theorem realPWLevel_starProjection_eq_evenExtension_comp {B : ℝ} (hB : 0 < B) :
    letI : CompleteSpace (realPWLevel B) := (isClosed_realPWLevel B).completeSpace_coe
    (realPWLevel B).starProjection =
      J₊.toContinuousLinearMap.comp
        ((physicalMeanZeroBandProjection B).comp J₊.toContinuousLinearMap.adjoint) := by
  let : CompleteSpace (realPWLevel B) := (isClosed_realPWLevel B).completeSpace_coe
  let K := (meanZeroFrequencyBand B).map (C₊.toLinearEquiv : H₊ →ₗ[ℂ] H₊)
  have hm : K.map J₊.toLinearMap = realPWLevel B := map_physicalMeanZeroBand_positiveRayEvenExtension hB
  apply ContinuousLinearMap.ext
  intro x
  let a := J₊.toContinuousLinearMap.adjoint x
  change (realPWLevel B).starProjection x = J₊ (K.starProjection a)
  apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero
  · rw [← hm]
    exact ⟨K.starProjection a, K.starProjection_apply_mem a, rfl⟩
  · intro y hy
    rw [← hm] at hy
    obtain ⟨k, hk, rfl⟩ := hy
    change inner ℂ (x - J₊ (K.starProjection a)) (J₊ k) = 0
    rw [inner_sub_left, J₊.inner_map_map]
    have hx : inner ℂ x (J₊ k) = inner ℂ a k :=
      (J₊.toContinuousLinearMap.adjoint_inner_left k x).symm
    rw [hx, ← inner_sub_left]
    exact Submodule.starProjection_inner_eq_zero _ _ hk

end RiemannMasullo.FlatPolar
