module

public import Mathlib.Analysis.Fourier.LpSpace
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff

@[expose] public noncomputable section

open Filter MeasureTheory

namespace RiemannMasullo

open scoped FourierTransform SchwartzMap
open Real in
/-- For an integrable L² class the Plancherel transform agrees almost everywhere
with the Fourier integral of its representative. -/
theorem fourier_L2_coeFn_of_integrable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
    (f : Lp (α := V) ℂ 2) (hf : Integrable (f : V → ℂ)) :
    (𝓕 f : Lp (α := V) ℂ 2) =ᵐ[volume] (𝓕 (f : V → ℂ)) := by
  have hcont : Continuous (𝓕 (f : V → ℂ)) := VectorFourier.fourierIntegral_continuous
    continuous_fourierChar (innerSL ℝ).continuous₂ hf
  apply ae_eq_of_integral_contDiff_smul_eq ((Lp.memLp (𝓕 f)).locallyIntegrable one_le_two)
    hcont.locallyIntegrable
  intro g hgd hgc
  have hφc : HasCompactSupport (Complex.ofRealCLM ∘ g) := hgc.comp_left rfl
  let φ := hφc.toSchwartzMap (Complex.ofRealCLM.contDiff.comp hgd)
  have h := congrArg (fun T : TemperedDistribution V ℂ ↦ T φ) (Lp.fourier_toTemperedDistribution_eq f)
  change Lp.toTemperedDistribution f (𝓕 φ) = Lp.toTemperedDistribution (𝓕 f) φ at h
  rw [Lp.toTemperedDistribution_apply, Lp.toTemperedDistribution_apply] at h
  have hi : (∫ x, (𝓕 φ) x • f x) = ∫ x, φ x • 𝓕 (f : V → ℂ) x := by
    simpa only [SchwartzMap.fourier_coe, flip_innerₗ] using! VectorFourier.integral_fourierIntegral_smul_eq_flip
      (L := innerₗ V) continuous_fourierChar continuous_inner (φ.integrable (μ := volume)) hf
  have hφ (x : V) : φ x = (g x : ℂ) := rfl
  simpa only [hφ, Complex.coe_smul] using h.symm.trans hi

end RiemannMasullo
