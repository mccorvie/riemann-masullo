module

public import Mathlib.Analysis.Fourier.LpSpace

@[expose] public section

namespace RiemannMasullo

open MeasureTheory
open scoped ContDiff ENNReal FourierTransform SchwartzMap

/-- On integrable square-integrable functions, the Fourier integral is square-integrable
and has the same `L²` norm as the original function. -/
theorem memLp_two_fourier_and_eLpNorm_eq {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
    {f : V → ℂ} (hf₁ : Integrable f) (hf₂ : MemLp f 2) :
    MemLp (𝓕 f) 2 ∧ eLpNorm (𝓕 f) 2 volume = eLpNorm f 2 volume := by
  let F : Lp ℂ 2 (volume : Measure V) := 𝓕 (hf₂.toLp f)
  -- The two transforms agree as distributions, hence almost everywhere.
  have hae : 𝓕 f =ᵐ[volume] (F : V → ℂ) := by
    apply ae_eq_of_integral_contDiff_smul_eq
    · exact (VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
        (innerSL ℝ).continuous₂ hf₁).locallyIntegrable
    · exact (Lp.memLp F).locallyIntegrable one_le_two
    intro g hg hc
    let gC : V → ℂ := Complex.ofRealCLM ∘ g
    have hcC : HasCompactSupport gC := hc.comp_left rfl
    have hgC : ContDiff ℝ ∞ gC := by unfold gC; fun_prop
    let φ := hcC.toSchwartzMap hgC
    have hF := congrArg (fun T : 𝓢'(V, ℂ) ↦ T φ)
      (Lp.fourier_toTemperedDistribution_eq (hf₂.toLp f))
    simp only [TemperedDistribution.fourier_apply, Lp.toTemperedDistribution_apply] at hF
    change (∫ x, φ x • 𝓕 f x) = ∫ x, φ x • F x
    calc
      _ = ∫ x, (𝓕 φ) x • f x := by
        simp_rw [smul_eq_mul, mul_comm (φ _) (𝓕 f _), mul_comm ((𝓕 φ) _) (f _),
          SchwartzMap.fourier_coe]
        simpa only [Real.instFourierTransform, FourierTransform.fourier, flip_innerₗ, smul_eq_mul]
          using VectorFourier.integral_fourierIntegral_smul_eq_flip (L := innerₗ V)
            Real.continuous_fourierChar continuous_inner hf₁ φ.integrable
      _ = ∫ x, (𝓕 φ) x • hf₂.toLp f x := by
        apply integral_congr_ae
        filter_upwards [hf₂.coeFn_toLp] with x hx
        rw [hx]
      _ = _ := hF
  refine ⟨(Lp.memLp F).ae_eq hae.symm, ?_⟩
  calc
    eLpNorm (𝓕 f) 2 volume = ‖F‖ₑ := (eLpNorm_congr_ae hae).trans (Lp.eNorm_def F).symm
    _ = ‖hf₂.toLp f‖ₑ := by
      rw [← ofReal_norm, ← ofReal_norm, Lp.norm_fourier_eq]
    _ = eLpNorm f 2 volume := (Lp.eNorm_def _).trans (eLpNorm_congr_ae hf₂.coeFn_toLp)

end RiemannMasullo
