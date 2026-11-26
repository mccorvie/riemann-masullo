module

public import RiemannMasullo.ForMathlib.Analysis.Fourier.Integrable
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff

/-! # Continuous representatives from the inverse `L²` Fourier transform

The inverse Plancherel transform agrees with the inverse Fourier integral on `L¹ ∩ L²`.
This recovers a continuous `L²` representative pointwise once its transform is integrable,
without requiring the original function itself to be integrable.
-/

@[expose] public noncomputable section
open Filter MeasureTheory FourierTransform
open scoped FourierTransform SchwartzMap
namespace RiemannMasullo

open Real in
/-- For an integrable `L²` class, the inverse Plancherel transform agrees almost everywhere
with the inverse Fourier integral. -/
theorem fourierInv_L2_coeFn_of_integrable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
    (f : Lp (α := V) ℂ 2) (hf : Integrable (f : V → ℂ)) :
    (𝓕⁻ f : Lp (α := V) ℂ 2) =ᵐ[volume] (𝓕⁻ (f : V → ℂ)) := by
  have hcont : Continuous (𝓕⁻ (f : V → ℂ)) := by
    change Continuous (VectorFourier.fourierIntegral Real.fourierChar volume (-(innerₗ V)) (f : V → ℂ))
    exact VectorFourier.fourierIntegral_continuous continuous_fourierChar continuous_inner.neg hf
  apply ae_eq_of_integral_contDiff_smul_eq ((Lp.memLp (𝓕⁻ f)).locallyIntegrable one_le_two)
    hcont.locallyIntegrable
  intro g hgd hgc
  have hφc : HasCompactSupport (Complex.ofRealCLM ∘ g) := hgc.comp_left rfl
  let φ := hφc.toSchwartzMap (Complex.ofRealCLM.contDiff.comp hgd)
  have h := congrArg (fun T : TemperedDistribution V ℂ ↦ T φ) (Lp.fourierInv_toTemperedDistribution_eq f)
  change Lp.toTemperedDistribution f (𝓕⁻ φ) = Lp.toTemperedDistribution (𝓕⁻ f) φ at h
  rw [Lp.toTemperedDistribution_apply, Lp.toTemperedDistribution_apply] at h
  have hi : (∫ x, (𝓕⁻ φ) x • f x) = ∫ x, φ x • 𝓕⁻ (f : V → ℂ) x := by
    have hflip : (-(innerₗ V)).flip = -(innerₗ V) := by
      ext x y
      simp [real_inner_comm]
    have hcoe (x : V) : (𝓕⁻ φ) x = 𝓕⁻ (φ : V → ℂ) x :=
      congrFun (SchwartzMap.fourierInv_coe φ) x
    simp_rw [hcoe]
    simpa only [Real.instFourierTransformInv, FourierTransformInv.fourierInv, hflip] using!
      VectorFourier.integral_fourierIntegral_smul_eq_flip (L := -(innerₗ V))
        continuous_fourierChar continuous_inner.neg (φ.integrable (μ := volume)) hf
  have hφ (x : V) : φ x = (g x : ℂ) := rfl
  simpa only [hφ, Complex.coe_smul] using h.symm.trans hi

/-- A continuous representative of an `L²` class is recovered pointwise by the inverse
Fourier integral when its Plancherel transform is integrable. -/
theorem continuous_eq_fourierInv_L2 {f : ℝ → ℂ} (hf : Continuous f) (hf₂ : MemLp f 2)
    (hF : Integrable ((𝓕 (hf₂.toLp f) : Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ)) :
    f = FourierTransformInv.fourierInv
      ((𝓕 (hf₂.toLp f) : Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ) := by
  have he := fourierInv_L2_coeFn_of_integrable (𝓕 (hf₂.toLp f)) hF
  rw [fourierInv_fourier_eq] at he
  have hcont : Continuous (FourierTransformInv.fourierInv
      ((𝓕 (hf₂.toLp f) : Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ)) := by
    change Continuous (VectorFourier.fourierIntegral Real.fourierChar volume (-(innerₗ ℝ))
      ((𝓕 (hf₂.toLp f) : Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ))
    exact VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar continuous_inner.neg hF
  exact Measure.eq_of_ae_eq (hf₂.coeFn_toLp.symm.trans he) hf hcont

end RiemannMasullo
