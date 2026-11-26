module

public import RiemannMasullo.ForMathlib.Analysis.Fourier.L2Inverse

@[expose] public noncomputable section
open MeasureTheory FourierTransform
open scoped FourierTransform
namespace RiemannMasullo

/-- The inverse Fourier integral of an integrable `L²` function represents its inverse
Plancherel transform, independently of the chosen representative. -/
theorem fourierInv_toLp_coeFn_of_integrable {f : ℝ → ℂ} (hf : MemLp f 2)
    (hi : Integrable f) :
    ((𝓕⁻ (hf.toLp f) : Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ) =ᵐ[volume] 𝓕⁻ f := by
  have hi' : Integrable (hf.toLp f : ℝ → ℂ) := hi.congr hf.coeFn_toLp.symm
  have he := fourierInv_L2_coeFn_of_integrable (hf.toLp f) hi'
  filter_upwards [he] with x hx
  rw [hx, Real.fourierInv_eq', Real.fourierInv_eq']
  apply integral_congr_ae
  filter_upwards [hf.coeFn_toLp] with ξ hξ
  rw [hξ]

/-- An integrable square-integrable Fourier density has a square-integrable inverse
Fourier integral. -/
theorem memLp_fourierInv_of_integrable {f : ℝ → ℂ} (hf : MemLp f 2) (hi : Integrable f) :
    MemLp (𝓕⁻ f) 2 :=
  (Lp.memLp (𝓕⁻ (hf.toLp f))).ae_eq (fourierInv_toLp_coeFn_of_integrable hf hi)

/-- Fourier transformation recovers the original `L²` density after inverse synthesis. -/
theorem fourier_toLp_fourierInv {f : ℝ → ℂ} (hf : MemLp f 2) (hi : Integrable f) :
    𝓕 ((memLp_fourierInv_of_integrable hf hi).toLp (𝓕⁻ f)) = hf.toLp f := by
  have he : (memLp_fourierInv_of_integrable hf hi).toLp (𝓕⁻ f) = 𝓕⁻ (hf.toLp f) := by
    apply Lp.ext
    exact (memLp_fourierInv_of_integrable hf hi).coeFn_toLp.trans
      (fourierInv_toLp_coeFn_of_integrable hf hi).symm
  rw [he, fourier_fourierInv_eq]

end RiemannMasullo
