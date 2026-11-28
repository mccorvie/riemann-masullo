module

public import RiemannMasullo.ForMathlib.MeasureTheory.Function.PositiveRayDilation
public import RiemannMasullo.ForMathlib.Analysis.Fourier.Integrable
import Mathlib.MeasureTheory.Measure.Lebesgue.Integral

/-!
# The inverse cosine transform on positive-ray Lebesgue space

The normalized even extension sends `f(t)` to `f(|x|)/√2`. The ordinary inverse
Plancherel transform preserves its even image. Restriction to the positive ray followed
by multiplication by `√2` gives the inverse cosine transform and takes dilation by
`a` to dilation by `a⁻¹`.
-/

@[expose] public noncomputable section

open Filter Function MeasureTheory Set Topology
open scoped ENNReal FourierTransform

namespace RiemannMasullo.FlatPolar

namespace FullLine

local notation "Hℝ" => Lp ℂ 2 (volume : Measure ℝ)

/-- A nonzero real scaling preserves Lebesgue null sets. -/
theorem scale_quasiMeasurePreserving (a : ℝ) (ha : a ≠ 0) :
    QuasiMeasurePreserving (fun t : ℝ ↦ a * t) volume volume :=
  ⟨(measurable_const_mul a).aemeasurable, by
    rw [Real.map_volume_mul_left ha]
    exact Measure.smul_absolutelyContinuous⟩

/-- Dilation of nonzero signed scale has the absolute square-root Jacobian on the full line. -/
theorem exists_dilation (a : ℝ) (ha : a ≠ 0) :
    ∃ T : Hℝ →ₗᵢ[ℂ] Hℝ, ∀ f : Hℝ, (T f : ℝ → ℂ) =ᵐ[volume] fun t ↦ (Real.sqrt |a| : ℂ) * f (a * t) := by
  let V (f : Hℝ) (t : ℝ) := (Real.sqrt |a| : ℂ) * f (a * t)
  have hmem (f : Hℝ) : MemLp (V f) 2 volume := by
    have hpush : MemLp (f : ℝ → ℂ) 2 ((volume).map (fun t ↦ a * t)) := by
      rw [Real.map_volume_mul_left ha]
      exact (Lp.memLp f).smul_measure ENNReal.ofReal_ne_top
    exact ((memLp_map_measure_iff hpush.aestronglyMeasurable
      (measurable_const_mul a).aemeasurable).mp hpush).const_mul _
  let T (f : Hℝ) := (hmem f).toLp (V f)
  have hT (f : Hℝ) : (T f : ℝ → ℂ) =ᵐ[volume] V f := (hmem f).coeFn_toLp
  have hscale := scale_quasiMeasurePreserving a ha
  refine ⟨{ toFun := T, map_add' := ?_, map_smul' := ?_, norm_map' := ?_ }, hT⟩
  · intro f g
    apply Lp.ext
    filter_upwards [hT (f+g), hT f, hT g, Lp.coeFn_add (T f) (T g),
      hscale.ae_eq_comp (Lp.coeFn_add f g)] with t h₁ h₂ h₃ h₄ h₅
    change (f + g) (a * t) = f (a * t) + g (a * t) at h₅
    rw [h₁, h₄]
    simp only [Pi.add_apply, V, h₂, h₃, h₅, mul_add]
  · intro c f
    apply Lp.ext
    filter_upwards [hT (c • f), hT f, Lp.coeFn_smul c (T f),
      hscale.ae_eq_comp (Lp.coeFn_smul c f)] with t h₁ h₂ h₃ h₄
    change (c • f) (a * t) = c * f (a * t) at h₄
    change T (c • f) t = (c • T f) t
    rw [h₁, h₃]
    simp only [Pi.smul_apply, smul_eq_mul, V, h₂, h₄]
    ring
  · intro f
    have heq : ‖T f‖ ^ 2 = ‖f‖ ^ 2 := by
      rw [← L2.integral_sq_norm (𝕜 := ℂ), ← L2.integral_sq_norm (𝕜 := ℂ)]
      calc
        _ = ∫ t : ℝ, |a| * ‖f (a * t)‖ ^ 2 := by
          apply integral_congr_ae
          filter_upwards [hT f] with t ht
          simp [ht, V, mul_pow, Real.sq_sqrt (abs_nonneg a)]
        _ = _ := by
          rw [integral_const_mul, Measure.integral_comp_mul_left (fun t ↦ ‖f t‖ ^ 2),
            smul_eq_mul, abs_inv, ← mul_assoc, mul_inv_cancel₀ (abs_ne_zero.mpr ha), one_mul]
    exact (sq_eq_sq₀ (norm_nonneg (T f)) (norm_nonneg f)).mp heq


/-- The normalized signed dilation on full-line Lebesgue L². -/
def dilation (a : ℝ) (ha : a ≠ 0) : Hℝ →ₗᵢ[ℂ] Hℝ := (exists_dilation a ha).choose

/-- The full-line dilation multiplies the scaled representative by the square-root Jacobian. -/
theorem dilation_apply (a : ℝ) (ha : a ≠ 0) (f : Hℝ) :
    (dilation a ha f : ℝ → ℂ) =ᵐ[volume] fun t ↦ (Real.sqrt |a| : ℂ) * f (a * t) :=
  (exists_dilation a ha).choose_spec f

private theorem fourier_normalizedScale (a : ℝ) (ha : a ≠ 0) (f : ℝ → ℂ) (y : ℝ) :
    𝓕 (fun x ↦ (Real.sqrt |a| : ℂ) * f (a * x)) y =
      (Real.sqrt |a⁻¹| : ℂ) * 𝓕 f (a⁻¹ * y) := by
  rw [Real.fourier_real_eq_integral_exp_smul, Real.fourier_real_eq_integral_exp_smul]
  let k (x : ℝ) := Complex.exp (↑(-2 * Real.pi * x * (a⁻¹ * y)) * Complex.I) * f x
  have hphase (x : ℝ) : -2 * Real.pi * x * y = -2 * Real.pi * (a * x) * (a⁻¹ * y) := by
    field_simp
  have hroot : Real.sqrt |a| * |a⁻¹| = Real.sqrt |a⁻¹| := by
    rw [abs_inv, Real.sqrt_inv]
    field_simp [(abs_pos.mpr ha).ne', (Real.sqrt_pos.2 (abs_pos.mpr ha)).ne']
    nlinarith [Real.sq_sqrt (abs_nonneg a)]
  have hrootC := congrArg (fun t : ℝ ↦ (t : ℂ)) hroot
  simp only [Complex.ofReal_mul] at hrootC
  calc
    _ = (Real.sqrt |a| : ℂ) * ∫ x : ℝ, k (a * x) := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      exact .of_forall fun x ↦ by
        dsimp only [k, smul_eq_mul]
        rw [hphase x]
        ring
    _ = _ := by
      rw [Measure.integral_comp_mul_left k, Complex.real_smul, ← mul_assoc, hrootC]
      rfl

/-- In the model of (12.4.1.7), p. 516, the physical action `a⁻¹ᐟ² f(x/a)` has
Fourier transform `a¹ᐟ² (𝓕 f)(a ξ)`. -/
theorem fourier_physicalDilation (f : ℝ → ℂ) {a : ℝ} (ha : 0 < a) (ξ : ℝ) :
    𝓕 (fun x : ℝ ↦ (Real.sqrt a : ℂ)⁻¹ * f (x / a)) ξ =
      (Real.sqrt a : ℂ) * 𝓕 f (a * ξ) := by
  simpa only [inv_inv, abs_inv, abs_of_pos ha, Real.sqrt_inv, Complex.ofReal_inv,
    inv_mul_eq_div] using fourier_normalizedScale a⁻¹ (inv_ne_zero ha.ne') f ξ

/-- Fourier transform changes a real dilation into dilation by the reciprocal scale,
including reflection at scale minus one. -/
theorem fourier_dilation (a : ℝ) (ha : a ≠ 0) (f : Hℝ) :
    𝓕 (dilation a ha f) = dilation a⁻¹ (inv_ne_zero ha) (𝓕 f) := by
  let P (g : Hℝ) := 𝓕 (dilation a ha g) = dilation a⁻¹ (inv_ne_zero ha) (𝓕 g)
  apply DenseRange.induction_on (p := P) (SchwartzMap.denseRange_toLpCLM (p := 2) ENNReal.ofNat_ne_top) f
  · exact isClosed_eq ((Lp.fourierTransformₗᵢ ℝ ℂ).continuous.comp (dilation a ha).continuous)
      ((dilation a⁻¹ (inv_ne_zero ha)).continuous.comp (Lp.fourierTransformₗᵢ ℝ ℂ).continuous)
  intro φ
  let g : Hℝ := φ.toLp 2
  change 𝓕 (dilation a ha g) = dilation a⁻¹ (inv_ne_zero ha) (𝓕 g)
  have hg : Integrable (g : ℝ → ℂ) := φ.integrable.congr (φ.coeFn_toLp 2 volume).symm
  have hDg : Integrable (dilation a ha g : ℝ → ℂ) :=
    ((hg.comp_mul_left' ha).const_mul (Real.sqrt |a| : ℂ)).congr (dilation_apply a ha g).symm
  apply Lp.ext
  filter_upwards [fourier_L2_coeFn_of_integrable _ hDg, dilation_apply a⁻¹ (inv_ne_zero ha) (𝓕 g),
    (scale_quasiMeasurePreserving a⁻¹ (inv_ne_zero ha)).ae_eq_comp (fourier_L2_coeFn_of_integrable g hg)] with y h₁ h₂ h₃
  change (𝓕 g : Hℝ) (a⁻¹ * y) = 𝓕 (g : ℝ → ℂ) (a⁻¹ * y) at h₃
  rw [h₁, h₂, h₃, Real.fourier_congr_ae (dilation_apply a ha g)]
  exact fourier_normalizedScale a ha g y

/-- Inverse Fourier transform changes a normalized dilation into the reciprocal dilation. -/
theorem fourierInv_dilation (a : ℝ) (ha : a ≠ 0) (f : Hℝ) :
    𝓕⁻ (dilation a ha f) = dilation a⁻¹ (inv_ne_zero ha) (𝓕⁻ f) := by
  apply (Lp.fourierTransformₗᵢ ℝ ℂ).injective
  change 𝓕 (𝓕⁻ (dilation a ha f)) = 𝓕 (dilation a⁻¹ (inv_ne_zero ha) (𝓕⁻ f))
  simp only [FourierTransform.fourier_fourierInv_eq, fourier_dilation, inv_inv]

end FullLine

/-- An almost-everywhere identity on the open ray pulls back along the absolute value to
a full-line Lebesgue almost-everywhere identity. -/
theorem positiveRay_ae_abs {P : ℝ → Prop} (h : ∀ᵐ t ∂volume.restrict (Ioi (0 : ℝ)), P t) :
    ∀ᵐ x ∂volume, P |x| := by
  have h' := (ae_restrict_iff' measurableSet_Ioi).mp h
  filter_upwards [h', (Measure.measurePreserving_neg (volume : Measure ℝ)).quasiMeasurePreserving.ae h',
    (volume : Measure ℝ).ae_ne (0 : ℝ)] with x h₁ h₂ h₃
  rcases lt_or_gt_of_ne h₃ with hx | hx
  · rw [abs_of_neg hx]
    exact h₂ (neg_pos.mpr hx)
  · rw [abs_of_pos hx]
    exact h₁ hx

/-- An integrable function on the positive ray extends by reflection to an integrable function
on the line. -/
theorem positiveRay_integrable_abs {E : Type*} [NormedAddCommGroup E]
    {f : ℝ → E} (hf : IntegrableOn f (Ioi 0)) :
    Integrable (fun x ↦ f |x|) := by
  have hp : IntegrableOn (fun x ↦ f |x|) (Ioi 0) :=
    hf.congr_fun (fun x hx ↦ by rw [abs_of_pos hx]) measurableSet_Ioi
  have hn : IntegrableOn (fun x ↦ f |x|) (Iic 0) := by
    rw [← Measure.map_neg_eq_self (volume : Measure ℝ)]
    let m : MeasurableEmbedding (fun x : ℝ ↦ -x) := (Homeomorph.neg ℝ).measurableEmbedding
    rw [m.integrableOn_map_iff]
    simp only [Function.comp_def, abs_neg, neg_preimage, neg_Iic, neg_zero]
    exact (integrableOn_Ici_iff_integrableOn_Ioi (by finiteness)).mpr hp
  simpa using hp.union hn

/-- An isometric even extension has representative f(|x|)/√2 on the real line. -/
theorem exists_positiveRayEvenExtension :
    ∃ J : Lp ℂ 2 (volume.restrict (Ioi (0 : ℝ))) →ₗᵢ[ℂ] Lp ℂ 2 (volume : Measure ℝ),
      ∀ f, (J f : ℝ → ℂ) =ᵐ[volume] fun x ↦ (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) * f |x| := by
  let s := (((Real.sqrt 2)⁻¹ : ℝ) : ℂ)
  have hs : ‖s‖ ^ 2 * 2 = 1 := by
    simp only [s, Complex.norm_real, Real.norm_of_nonneg (by positivity : 0 ≤ (Real.sqrt 2)⁻¹),
      inv_pow, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]
    norm_num
  let H := Lp ℂ 2 (volume.restrict (Ioi (0 : ℝ)))
  let raw (f : H) (x : ℝ) := s * f |x|
  have hm (f : H) : MemLp (raw f) 2 volume := by
    apply MemLp.const_mul
    apply (memLp_two_iff_integrable_sq_norm
      (((Lp.stronglyMeasurable f).measurable.comp continuous_abs.measurable).aestronglyMeasurable)).2
    exact positiveRay_integrable_abs ((memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable f)).mp (Lp.memLp f))
  let J (f : H) := (hm f).toLp (raw f)
  have hJ (f : H) : (J f : ℝ → ℂ) =ᵐ[volume] raw f := (hm f).coeFn_toLp
  refine ⟨{ toFun := J, map_add' := ?_, map_smul' := ?_, norm_map' := ?_ }, hJ⟩
  · intro f g
    apply Lp.ext
    filter_upwards [hJ (f+g), hJ f, hJ g, Lp.coeFn_add (J f) (J g),
      positiveRay_ae_abs (Lp.coeFn_add f g)] with x h₁ h₂ h₃ h₄ h₅
    simp only [Pi.add_apply] at h₅
    simp only [h₁, h₄, Pi.add_apply, raw, h₂, h₃, h₅, mul_add]
  · intro z f
    apply Lp.ext
    filter_upwards [hJ (z • f), hJ f, Lp.coeFn_smul z (J f), positiveRay_ae_abs (Lp.coeFn_smul z f)]
      with x h₁ h₂ h₃ h₄
    change J (z • f) x = (z • J f) x
    simp only [Pi.smul_apply, smul_eq_mul] at h₄
    simp only [h₁, h₃, Pi.smul_apply, smul_eq_mul, raw, h₂, h₄]
    ring
  · intro f
    change ‖J f‖ = ‖f‖
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    rw [← L2.integral_sq_norm (𝕜 := ℂ), ← L2.integral_sq_norm (𝕜 := ℂ)]
    calc
      _ = ∫ x : ℝ, ‖s‖ ^ 2 * ‖f |x|‖ ^ 2 := by
        apply integral_congr_ae
        filter_upwards [hJ f] with x hx
        simp [hx, raw, mul_pow]
      _ = _ := by
        rw [integral_const_mul, integral_comp_abs (f := fun x ↦ ‖f x‖ ^ 2),
          ← mul_assoc, hs, one_mul]

/-- The normalized even extension embeds the positive-ray Hilbert space into full-line L². -/
def positiveRayEvenExtension :
    Lp ℂ 2 (volume.restrict (Ioi (0 : ℝ))) →ₗᵢ[ℂ] Lp ℂ 2 (volume : Measure ℝ) :=
  exists_positiveRayEvenExtension.choose

/-- Pointwise representative of the normalized even extension. -/
theorem positiveRayEvenExtension_apply (f : Lp ℂ 2 (volume.restrict (Ioi (0 : ℝ)))) :
    (positiveRayEvenExtension f : ℝ → ℂ) =ᵐ[volume]
      fun x ↦ (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) * f |x| :=
  exists_positiveRayEvenExtension.choose_spec f

/-- Every almost-everywhere even full-line L² vector has a preimage in the positive ray. -/
theorem mem_range_positiveRayEvenExtension_of_even (g : Lp ℂ 2 (volume : Measure ℝ))
    (hg : (fun x : ℝ ↦ g (-x)) =ᵐ[volume] g) :
    ∃ f, positiveRayEvenExtension f = g := by
  have hmem : MemLp (fun t ↦ (Real.sqrt 2 : ℂ) * g t) 2 (volume.restrict (Ioi (0 : ℝ))) :=
    ((Lp.memLp g).mono_measure Measure.restrict_le_self).const_mul _
  let f := hmem.toLp _
  refine ⟨f, Lp.ext ?_⟩
  filter_upwards [positiveRayEvenExtension_apply f, positiveRay_ae_abs hmem.coeFn_toLp, hg]
    with x h₁ h₂ h₃
  rw [h₁, h₂, ← mul_assoc, Complex.ofReal_inv, inv_mul_cancel₀ (Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr (by norm_num : (0:ℝ) < 2)).ne'), one_mul]
  rcases le_or_gt 0 x with hx | hx
  · rw [abs_of_nonneg hx]
  · rwa [abs_of_neg hx]

/-- Positive scaling of the normalized even extension is the full-line dilation. -/
theorem positiveRayEvenExtension_dilation (a : ℝ) (ha : 0 < a)
    (f : Lp ℂ 2 (volume.restrict (Ioi (0 : ℝ)))) :
    positiveRayEvenExtension (positiveRayDilation a ha f) = FullLine.dilation a ha.ne' (positiveRayEvenExtension f) := by
  apply Lp.ext
  filter_upwards [positiveRayEvenExtension_apply (positiveRayDilation a ha f),
    positiveRay_ae_abs (positiveRayDilation_apply a ha f), FullLine.dilation_apply a ha.ne' (positiveRayEvenExtension f),
    (FullLine.scale_quasiMeasurePreserving a ha.ne').ae_eq_comp (positiveRayEvenExtension_apply f)]
    with x h₁ h₂ h₃ h₄
  change positiveRayEvenExtension f (a * x) = (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) * f |a * x| at h₄
  rw [h₁, h₂, h₃, h₄, abs_mul, abs_of_pos ha]
  ring

private theorem evenExtension_reflection (f : Lp ℂ 2 (volume.restrict (Ioi (0 : ℝ)))) :
    FullLine.dilation (-1) (by norm_num) (positiveRayEvenExtension f) = positiveRayEvenExtension f := by
  apply Lp.ext
  filter_upwards [FullLine.dilation_apply (-1) (by norm_num) (positiveRayEvenExtension f),
    (Measure.measurePreserving_neg (volume : Measure ℝ)).quasiMeasurePreserving.ae_eq_comp (positiveRayEvenExtension_apply f),
    positiveRayEvenExtension_apply f] with x h₁ h₂ h₃
  change positiveRayEvenExtension f (-x) = (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) * f |-x| at h₂
  simpa only [h₁, abs_neg, abs_one, Real.sqrt_one, Complex.ofReal_one, neg_one_mul, one_mul, h₃] using h₂

/-- Extend evenly with normalization 1/√2, then apply the full inverse Plancherel transform. -/
def positiveRayInverseFourierEmbedding :
    Lp ℂ 2 (volume.restrict (Ioi (0 : ℝ))) →ₗᵢ[ℂ] Lp ℂ 2 (volume : Measure ℝ) :=
  (Lp.fourierTransformₗᵢ ℝ ℂ).symm.toLinearIsometry.comp positiveRayEvenExtension

/-- The embedding is the actual Mathlib inverse Fourier transform of the even extension. -/
theorem positiveRayInverseFourierEmbedding_apply (f : Lp ℂ 2 (volume.restrict (Ioi (0 : ℝ)))) :
    positiveRayInverseFourierEmbedding f = 𝓕⁻ (positiveRayEvenExtension f) := rfl

/-- Scaling before the inverse Fourier embedding is reciprocal scaling on the full line. -/
theorem positiveRayInverseFourierEmbedding_dilation (a : ℝ) (ha : 0 < a)
    (f : Lp ℂ 2 (volume.restrict (Ioi (0 : ℝ)))) :
    positiveRayInverseFourierEmbedding (positiveRayDilation a ha f) =
      FullLine.dilation a⁻¹ (inv_ne_zero ha.ne') (positiveRayInverseFourierEmbedding f) := by
  rw [positiveRayInverseFourierEmbedding_apply, positiveRayEvenExtension_dilation, FullLine.fourierInv_dilation]
  rfl

private theorem inverseEmbedding_even (f : Lp ℂ 2 (volume.restrict (Ioi (0 : ℝ)))) :
    (fun x : ℝ ↦ positiveRayInverseFourierEmbedding f (-x)) =ᵐ[volume] positiveRayInverseFourierEmbedding f := by
  have h := FullLine.fourierInv_dilation (-1) (by norm_num) (positiveRayEvenExtension f)
  rw [evenExtension_reflection] at h
  have hf : FullLine.dilation (-1) (by norm_num) (positiveRayInverseFourierEmbedding f) =
      positiveRayInverseFourierEmbedding f := by
    simpa only [positiveRayInverseFourierEmbedding_apply, inv_neg, inv_one] using h.symm
  have hh := FullLine.dilation_apply (-1) (by norm_num) (positiveRayInverseFourierEmbedding f)
  rw [hf] at hh
  simpa only [abs_neg, abs_one, Real.sqrt_one, Complex.ofReal_one, neg_one_mul, one_mul] using hh.symm

/-- The inverse Plancherel embedding of the ray has even range, giving an isometric
inverse cosine transform from the ray to itself. -/
theorem exists_positiveRayInverseCosine :
    ∃ U : Lp ℂ 2 (volume.restrict (Ioi (0 : ℝ))) →ₗᵢ[ℂ] Lp ℂ 2 (volume.restrict (Ioi (0 : ℝ))),
      ∀ f, positiveRayEvenExtension (U f) = positiveRayInverseFourierEmbedding f := by
  choose U hU using fun f ↦ mem_range_positiveRayEvenExtension_of_even
    (positiveRayInverseFourierEmbedding f) (inverseEmbedding_even f)
  refine ⟨{ toFun := U, map_add' := ?_, map_smul' := ?_, norm_map' := ?_ }, hU⟩
  · intro f g
    apply positiveRayEvenExtension.injective
    rw [hU, map_add, map_add, hU, hU]
  · intro c f
    apply positiveRayEvenExtension.injective
    change positiveRayEvenExtension (U (c • f)) = positiveRayEvenExtension (c • U f)
    rw [hU, map_smul, map_smul, hU]
  · intro f
    change ‖U f‖ = ‖f‖
    rw [← positiveRayEvenExtension.norm_map (U f), hU, positiveRayInverseFourierEmbedding.norm_map]

/-- The positive-ray inverse cosine transform is the normalized restriction of the
inverse Plancherel transform of the normalized even extension. -/
def positiveRayInverseCosine :
    Lp ℂ 2 (volume.restrict (Ioi (0 : ℝ))) →ₗᵢ[ℂ] Lp ℂ 2 (volume.restrict (Ioi (0 : ℝ))) :=
  exists_positiveRayInverseCosine.choose

/-- Extending the inverse cosine chart evenly recovers its full-line inverse Fourier model. -/
theorem positiveRayInverseCosine_evenExtension (f : Lp ℂ 2 (volume.restrict (Ioi (0 : ℝ)))) :
    positiveRayEvenExtension (positiveRayInverseCosine f) = positiveRayInverseFourierEmbedding f :=
  exists_positiveRayInverseCosine.choose_spec f

/-- On the positive ray the inverse cosine transform is √2 times the full inverse Fourier
transform of the normalized even extension. -/
theorem positiveRayInverseCosine_apply (f : Lp ℂ 2 (volume.restrict (Ioi (0 : ℝ)))) :
    (positiveRayInverseCosine f : ℝ → ℂ) =ᵐ[volume.restrict (Ioi (0 : ℝ))]
      fun x ↦ (Real.sqrt 2 : ℂ) * (𝓕⁻ (positiveRayEvenExtension f) : Lp ℂ 2 (volume : Measure ℝ)) x := by
  have h := positiveRayEvenExtension_apply (positiveRayInverseCosine f)
  rw [positiveRayInverseCosine_evenExtension, positiveRayInverseFourierEmbedding_apply] at h
  filter_upwards [ae_mono (Measure.restrict_le_self (s := Ioi (0 : ℝ))) h,
      ae_restrict_mem (μ := (volume : Measure ℝ)) (s := Ioi (0 : ℝ)) measurableSet_Ioi]
    with x hx hxpos
  rw [hx, abs_of_pos hxpos, ← mul_assoc, Complex.ofReal_inv,
    mul_inv_cancel₀ (Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2)).ne'), one_mul]

/-- The inverse cosine transform interchanges every positive dilation with its reciprocal. -/
theorem positiveRayInverseCosine_dilation (a : ℝ) (ha : 0 < a)
    (f : Lp ℂ 2 (volume.restrict (Ioi (0 : ℝ)))) :
    positiveRayInverseCosine (positiveRayDilation a ha f) =
      positiveRayDilation a⁻¹ (inv_pos.mpr ha) (positiveRayInverseCosine f) := by
  apply positiveRayEvenExtension.injective
  rw [positiveRayInverseCosine_evenExtension, positiveRayInverseFourierEmbedding_dilation,
    positiveRayEvenExtension_dilation, positiveRayInverseCosine_evenExtension]

/-- The inverse cosine transform maps onto the positive-ray Hilbert space. -/
theorem positiveRayInverseCosine_surjective : Function.Surjective positiveRayInverseCosine := by
  intro f
  have h := FullLine.fourier_dilation (-1) (by norm_num) (positiveRayEvenExtension f)
  rw [evenExtension_reflection] at h
  have hf : FullLine.dilation (-1) (by norm_num) (𝓕 (positiveRayEvenExtension f)) =
      𝓕 (positiveRayEvenExtension f) := by
    simpa only [inv_neg, inv_one] using h.symm
  have hh := FullLine.dilation_apply (-1) (by norm_num) (𝓕 (positiveRayEvenExtension f))
  rw [hf] at hh
  have he : (fun x : ℝ ↦ 𝓕 (positiveRayEvenExtension f) (-x)) =ᵐ[volume]
      (𝓕 (positiveRayEvenExtension f) : Lp ℂ 2 (volume : Measure ℝ)) := by
    simpa only [abs_neg, abs_one, Real.sqrt_one, Complex.ofReal_one, neg_one_mul, one_mul] using hh.symm
  obtain ⟨g, hg⟩ := mem_range_positiveRayEvenExtension_of_even _ he
  refine ⟨g, positiveRayEvenExtension.injective ?_⟩
  rw [positiveRayInverseCosine_evenExtension, positiveRayInverseFourierEmbedding_apply, hg,
    FourierTransform.fourierInv_fourier_eq]

/-- The unitary inverse cosine transform on the positive ray. -/
def positiveRayInverseCosineEquiv :
    Lp ℂ 2 (volume.restrict (Ioi (0 : ℝ))) ≃ₗᵢ[ℂ] Lp ℂ 2 (volume.restrict (Ioi (0 : ℝ))) :=
  LinearIsometryEquiv.ofSurjective positiveRayInverseCosine positiveRayInverseCosine_surjective

@[simp]
theorem positiveRayInverseCosineEquiv_apply (f : Lp ℂ 2 (volume.restrict (Ioi (0 : ℝ)))) :
    positiveRayInverseCosineEquiv f = positiveRayInverseCosine f := rfl

end RiemannMasullo.FlatPolar
