module

public import RiemannMasullo.ForMathlib.Analysis.Fourier.BesselCardinal.CutoffEndpoint
public import RiemannMasullo.ForMathlib.Analysis.Fourier.BesselCardinal.AngularGram
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.Tactic

open Set MeasureTheory Filter
open scoped FourierTransform SchwartzMap Real Topology NNReal ENNReal

@[expose] public noncomputable section

namespace RiemannMasullo.WeakCardinal

local notation "H" => Lp ℂ 2 (volume : Measure ℝ)
local notation "HA" => Lp ℂ 2 angularMeasure

def cyclesToAngular : ℝ ≃ᵐ ℝ := MeasurableEquiv.mulLeft₀ (2*Real.pi) (by positivity)

theorem measurePreserving_cyclesToAngular : MeasurePreserving cyclesToAngular volume angularMeasure := by
  refine ⟨cyclesToAngular.measurable, ?_⟩
  change Measure.map ((2*Real.pi) * ·) volume = _
  rw [Real.map_volume_mul_left (by positivity : 2*Real.pi ≠ 0), abs_of_pos (by positivity)]
  change ENNReal.ofReal (2*Real.pi)⁻¹ • (volume : Measure ℝ) = (angularFactor : ℝ≥0∞) • volume
  congr 1
  exact ENNReal.ofReal_eq_coe_nnreal (by positivity)

theorem undo_pullback {μ ν : Measure ℝ} (e : ℝ ≃ᵐ ℝ) (he : MeasurePreserving e μ ν)
    (f : Lp ℂ 2 ν) :
    Lp.compMeasurePreserving e.symm he.symm (Lp.compMeasurePreserving e he f) = f := by
  apply Lp.ext
  filter_upwards [Lp.coeFn_compMeasurePreserving (Lp.compMeasurePreserving e he f) he.symm,
    he.symm.quasiMeasurePreserving.ae (Lp.coeFn_compMeasurePreserving f he)] with x h₁ h₂
  exact h₁.trans (h₂.trans (congrArg (⇑f) (e.apply_symm_apply x)))

/-- Pull back the normalized angular measure by `ξ ↦ 2πξ`. -/
def angularToCycles : HA ≃ₗᵢ[ℂ] H := LinearIsometryEquiv.ofLinearIsometry
  (Lp.compMeasurePreservingₗᵢ (E := ℂ) (p := 2) ℂ _ measurePreserving_cyclesToAngular)
  (Lp.compMeasurePreservingₗ (E := ℂ) (p := 2) ℂ _ measurePreserving_cyclesToAngular.symm)
  (by ext f : 1; exact undo_pullback cyclesToAngular.symm measurePreserving_cyclesToAngular.symm f)
  (by ext f : 1; exact undo_pullback cyclesToAngular measurePreserving_cyclesToAngular f)

theorem angularToCycles_apply_ae (f : HA) :
    (angularToCycles f : ℝ → ℂ) =ᵐ[volume] fun ξ ↦ f (2*Real.pi*ξ) :=
  Lp.coeFn_compMeasurePreserving f measurePreserving_cyclesToAngular

private theorem angularToCycles_symm_apply_ae (f : H) :
    (angularToCycles.symm f : ℝ → ℂ) =ᵐ[angularMeasure] fun ξ ↦ f (cyclesToAngular.symm ξ) :=
  Lp.coeFn_compMeasurePreserving f measurePreserving_cyclesToAngular.symm

/-- Physical multiplication in the positive-phase inverse angular representation. -/
def angularScaledCutoffQuotient (w : ℝ) {R : ℝ} (hR : 0 < R) : HA →L[ℂ] HA :=
  (angularToCycles.symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
    (fourierScaledCutoffQuotient w hR)).comp angularToCycles.toContinuousLinearEquiv.toContinuousLinearMap

theorem angularScaledCutoffQuotient_norm_le (w : ℝ) {R : ℝ} (hR : 0 < R) :
    ‖angularScaledCutoffQuotient w hR‖ ≤ (9/8)/R := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro f
  change ‖angularToCycles.symm (fourierScaledCutoffQuotient w hR (angularToCycles f))‖ ≤ _
  rw [LinearIsometryEquiv.norm_map]
  simpa only [LinearIsometryEquiv.norm_map] using
    (fourierScaledCutoffQuotient w hR).le_of_opNorm_le (fourierScaledCutoffQuotient_norm_le w hR) (angularToCycles f)

theorem angularScaledCutoffQuotient_full_endpoint (w : ℝ) {R : ℝ} (hR : 0 < R) (f j : HA)
    (hj : (j : ℝ → ℂ) =ᵐ[angularMeasure] fun ξ ↦ (1+ξ^2) • f ξ) :
    ∃ k : HA, (k : ℝ → ℂ) =ᵐ[angularMeasure] (fun ξ ↦ (1+ξ^2) • angularScaledCutoffQuotient w hR f ξ) ∧
      ‖k‖ ≤ ((9/8)/R + 2/R^2 + 6/R^3)*‖j‖ := by
  have hc : (angularToCycles j : ℝ → ℂ) =ᵐ[volume] fun ξ ↦ (1+(2*Real.pi*ξ)^2) • angularToCycles f ξ := by
    filter_upwards [angularToCycles_apply_ae j, angularToCycles_apply_ae f,
      measurePreserving_cyclesToAngular.quasiMeasurePreserving.ae hj] with ξ h₁ h₂ h₃
    rw [h₁, h₂]
    exact h₃
  obtain ⟨k, hk, hn⟩ := fourierScaledCutoffQuotient_full_endpoint w hR _ _ hc
  refine ⟨angularToCycles.symm k, ?_, by simpa only [LinearIsometryEquiv.norm_map] using hn⟩
  filter_upwards [angularToCycles_symm_apply_ae k,
    angularToCycles_symm_apply_ae (fourierScaledCutoffQuotient w hR (angularToCycles f)),
    measurePreserving_cyclesToAngular.symm.quasiMeasurePreserving.ae hk] with ξ h₁ h₂ h₃
  change _ = _ • (angularToCycles.symm (fourierScaledCutoffQuotient w hR (angularToCycles f))) ξ
  rw [h₁, h₂, h₃]
  rw [show 2*Real.pi*(cyclesToAngular.symm ξ) = ξ from cyclesToAngular.apply_symm_apply ξ]

theorem angularScaledCutoffQuotient_full_endpoint_six (w : ℝ) (f j : HA)
    (hj : (j : ℝ → ℂ) =ᵐ[angularMeasure] fun ξ ↦ (1+ξ^2) • f ξ) :
    ∃ k : HA, (k : ℝ → ℂ) =ᵐ[angularMeasure] (fun ξ ↦ (1+ξ^2) •
      angularScaledCutoffQuotient w (R := 6) (by norm_num) f ξ) ∧ ‖k‖ ≤ (13/48)*‖j‖ := by
  simpa only [radius_six_multiplier_constant] using angularScaledCutoffQuotient_full_endpoint w
    (R := 6) (by norm_num) f j hj


/-- Plancherel inversion agrees with the continuous positive-phase integral for
an integrable representative. -/
private theorem fourierInv_L2_coeFn_of_integrable (f : H) (hf : Integrable (f : ℝ → ℂ)) :
    (𝓕⁻ f : H) =ᵐ[volume] 𝓕⁻ (f : ℝ → ℂ) := by
  have hcont : Continuous (𝓕⁻ (f : ℝ → ℂ)) :=
    VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar continuous_inner.neg hf
  apply ae_eq_of_integral_contDiff_smul_eq ((Lp.memLp (𝓕⁻ f)).locallyIntegrable one_le_two) hcont.locallyIntegrable
  intro g hgd hgc
  have hφc : HasCompactSupport (Complex.ofRealCLM ∘ g) := hgc.comp_left rfl
  let φ := hφc.toSchwartzMap (Complex.ofRealCLM.contDiff.comp hgd)
  have h := congrArg (fun T : TemperedDistribution ℝ ℂ ↦ T φ) (Lp.fourierInv_toTemperedDistribution_eq f)
  change Lp.toTemperedDistribution f (𝓕⁻ φ) = Lp.toTemperedDistribution (𝓕⁻ f) φ at h
  rw [Lp.toTemperedDistribution_apply, Lp.toTemperedDistribution_apply] at h
  have hflip : (-innerₗ ℝ).flip = -innerₗ ℝ := by ext; simp
  have hi : (∫ x, (𝓕⁻ φ) x • f x) = ∫ x, φ x • 𝓕⁻ (f : ℝ → ℂ) x := by
    simpa only [SchwartzMap.fourierInv_coe, hflip] using!
      VectorFourier.integral_fourierIntegral_smul_eq_flip (L := -innerₗ ℝ)
        Real.continuous_fourierChar continuous_inner.neg (φ.integrable (μ := volume)) hf
  have hφ (x : ℝ) : φ x = (g x : ℂ) := rfl
  simpa only [hφ, Complex.coe_smul] using h.symm.trans hi

private theorem inverse_integral_angular (f : HA) (x : ℝ) :
    (𝓕⁻ (angularToCycles f : ℝ → ℂ)) x = ∫ ξ, phase x ξ * f ξ ∂angularMeasure := by
  rw [← measurePreserving_cyclesToAngular.integral_comp' (fun ξ ↦ phase x ξ * f ξ),
    Real.fourierInv_eq_fourier_neg, Real.fourier_real_eq_integral_exp_smul]
  apply integral_congr_ae
  filter_upwards [angularToCycles_apply_ae f] with ξ hξ
  rw [hξ, phase, Circle.coe_exp, smul_eq_mul]
  change Complex.exp (_ * Complex.I) * _ = Complex.exp (((x*(2*Real.pi*ξ) : ℝ) : ℂ) * Complex.I) * _
  congr 3
  push_cast
  ring

/-- The angular inverse transform is a continuous representative of the physical
Plancherel inverse whenever its input is integrable in angular measure. -/
theorem angularInverse_eq_ae_and_continuous (f : HA) (hf : Integrable (f : ℝ → ℂ) angularMeasure) :
    (𝓕⁻ (angularToCycles f) : H) =ᵐ[volume] (fun x ↦ ∫ ξ, phase x ξ * f ξ ∂angularMeasure) ∧
      Continuous (fun x ↦ ∫ ξ, phase x ξ * f ξ ∂angularMeasure) := by
  have hif : Integrable (angularToCycles f : ℝ → ℂ) :=
    (measurePreserving_cyclesToAngular.integrable_comp_of_integrable hf).congr (angularToCycles_apply_ae f).symm
  have h := funext (inverse_integral_angular f)
  rw [← h]
  exact ⟨fourierInv_L2_coeFn_of_integrable _ hif,
    VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar continuous_inner.neg hif⟩

/-- Pointwise multiplication on the actual angular inverse transforms, for each
real spatial point, using the same operator as the weighted endpoint. -/
theorem angularInverse_scaledCutoffQuotient (w : ℝ) {R : ℝ} (hR : 0 < R) (f : HA)
    (hf : Integrable (f : ℝ → ℂ) angularMeasure)
    (ht : Integrable (angularScaledCutoffQuotient w hR f : ℝ → ℂ) angularMeasure) (x : ℝ) :
    (∫ ξ, phase x ξ * angularScaledCutoffQuotient w hR f ξ ∂angularMeasure) =
      scaledCutoffQuotient w R x • (∫ ξ, phase x ξ * f ξ ∂angularMeasure) := by
  let t := angularScaledCutoffQuotient w hR f
  obtain ⟨hft, hct⟩ := angularInverse_eq_ae_and_continuous t ht
  obtain ⟨hff, hcf⟩ := angularInverse_eq_ae_and_continuous f hf
  have he : (𝓕⁻ (angularToCycles t) : H) = scaledCutoffQuotientL2 w hR (𝓕⁻ (angularToCycles f)) := by
    change (Lp.fourierTransformₗᵢ ℝ ℂ).symm
      (angularToCycles (angularToCycles.symm ((Lp.fourierTransformₗᵢ ℝ ℂ) _))) = _
    rw [LinearIsometryEquiv.apply_symm_apply, LinearIsometryEquiv.symm_apply_apply]
    rfl
  rw [he] at hft
  have ha : Continuous (scaledCutoffQuotient w R) := continuous_iff_continuousAt.mpr
    (fun y ↦ (hasDerivAt_scaledCutoffQuotient w R y).continuousAt)
  apply congrFun (Measure.eq_of_ae_eq (μ := volume) _ hct (ha.smul hcf)) x
  filter_upwards [hft, hff, scaledCutoffQuotientL2_apply_ae w hR (𝓕⁻ (angularToCycles f))] with y hy hy' hy''
  exact hy.symm.trans (hy''.trans (congrArg _ hy'))

end RiemannMasullo.WeakCardinal
