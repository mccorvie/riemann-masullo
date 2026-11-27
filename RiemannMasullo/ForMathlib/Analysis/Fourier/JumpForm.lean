module

public import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Integral.Prod

/-! # Fourier representation of translation jump forms -/

public section

open MeasureTheory
open scoped ENNReal FourierTransform SchwartzMap

namespace RiemannMasullo

private theorem schwartz_integrable_norm_sq (f : 𝓢(ℝ, ℂ)) :
    Integrable (fun x ↦ ‖f x‖ ^ 2) := by
  simpa using (f.memLp (2 : ℝ≥0∞) volume).integrable_norm_rpow
    (by norm_num) (by simp)

private theorem schwartz_fourier_compSubConst (f : 𝓢(ℝ, ℂ)) (h ξ : ℝ) :
    𝓕 (f.compSubConstCLM ℂ (-h)) ξ = (𝐞 (h * ξ) : ℂ) * 𝓕 f ξ := by
  simp only [SchwartzMap.fourier_coe]
  convert congrFun (Fourier.fourierIntegral_comp_add_right 𝐞 volume (f : ℝ → ℂ) h) ξ
    using 1 <;> simp [Real.fourier_eq, Fourier.fourierIntegral, VectorFourier.fourierIntegral,
      sub_neg_eq_add, Circle.smul_def, mul_comm ξ]

private theorem schwartz_lintegral_norm_sq_fourier (f : 𝓢(ℝ, ℂ)) :
    (∫⁻ x, ENNReal.ofReal (‖f x‖ ^ 2)) =
      ∫⁻ ξ, ENNReal.ofReal (‖𝓕 f ξ‖ ^ 2) := by
  rw [← ofReal_integral_eq_lintegral_ofReal (schwartz_integrable_norm_sq f)
      (ae_of_all _ fun _ ↦ sq_nonneg _),
    ← ofReal_integral_eq_lintegral_ofReal (schwartz_integrable_norm_sq (𝓕 f))
      (ae_of_all _ fun _ ↦ sq_nonneg _),
    SchwartzMap.integral_norm_sq_fourier]

/-- The squared (L^2) norm of a Schwartz translation difference is the Fourier
energy weighted by the squared character difference. -/
theorem schwartz_lintegral_sq_translate_sub (f : 𝓢(ℝ, ℂ)) (h : ℝ) :
    (∫⁻ x, ENNReal.ofReal (‖f (x + h) - f x‖ ^ 2)) =
      ∫⁻ ξ, ENNReal.ofReal (‖(𝐞 (h * ξ) : ℂ) - 1‖ ^ 2) *
        ENNReal.ofReal (‖𝓕 f ξ‖ ^ 2) := by
  let d := f.compSubConstCLM ℂ (-h) - f
  calc
    _ = ∫⁻ x, ENNReal.ofReal (‖d x‖ ^ 2) := by
      simp [d, sub_neg_eq_add]
    _ = ∫⁻ ξ, ENNReal.ofReal (‖𝓕 d ξ‖ ^ 2) := schwartz_lintegral_norm_sq_fourier d
    _ = _ := by
      apply lintegral_congr fun ξ ↦ ?_
      have he : 𝓕 d ξ = ((𝐞 (h * ξ) : ℂ) - 1) * 𝓕 f ξ := by
        simp [d, schwartz_fourier_compSubConst, sub_mul]
      rw [he, norm_mul, mul_pow, ENNReal.ofReal_mul (sq_nonneg _)]

/-- A translation jump measure with the stated Fourier symbol gives precisely the
Schwartz fractional Sobolev energy. The measure is on displacements, and the
physical frequency corresponding to Mathlib's variable `ξ` is `2 * π * ξ`. -/
theorem schwartz_fractional_energy_eq_of_jump_symbol
    (f : 𝓢(ℝ, ℂ)) (s : ℝ) (hs : 0 ≤ s) (μ : Measure ℝ) [SFinite μ]
    (hsymbol : ∀ ξ : ℝ,
      (2 : ℝ≥0∞)⁻¹ * (∫⁻ h, ENNReal.ofReal (‖(𝐞 (h * ξ) : ℂ) - 1‖ ^ 2) ∂μ) =
        ENNReal.ofReal ((1 + (2 * Real.pi * ξ) ^ 2) ^ s - 1)) :
    (∫⁻ x, ENNReal.ofReal (‖f x‖ ^ 2)) +
        (2 : ℝ≥0∞)⁻¹ * (∫⁻ h, (∫⁻ x, ENNReal.ofReal (‖f (x + h) - f x‖ ^ 2)) ∂μ) =
      ∫⁻ ξ, ENNReal.ofReal ((1 + (2 * Real.pi * ξ) ^ 2) ^ s) *
        ENNReal.ofReal (‖𝓕 f ξ‖ ^ 2) := by
  let a (ξ : ℝ) := ENNReal.ofReal (‖𝓕 f ξ‖ ^ 2)
  let b (h ξ : ℝ) := ENNReal.ofReal (‖(𝐞 (h * ξ) : ℂ) - 1‖ ^ 2)
  let w (ξ : ℝ) := (1 + (2 * Real.pi * ξ) ^ 2) ^ s
  have ha : Measurable a := ENNReal.measurable_ofReal.comp
    (by fun_prop : Continuous (fun ξ ↦ ‖𝓕 f ξ‖ ^ 2)).measurable
  have hb : Measurable (Function.uncurry b) := ENNReal.measurable_ofReal.comp
    (by fun_prop : Continuous (fun z : ℝ × ℝ ↦ ‖(𝐞 (z.1 * z.2) : ℂ) - 1‖ ^ 2)).measurable
  have hj : (∫⁻ h, (∫⁻ x, ENNReal.ofReal (‖f (x + h) - f x‖ ^ 2)) ∂μ) =
      ∫⁻ ξ, (∫⁻ h, b h ξ ∂μ) * a ξ := by
    simp_rw [schwartz_lintegral_sq_translate_sub]
    change (∫⁻ h, (∫⁻ ξ, b h ξ * a ξ) ∂μ) = _
    rw [lintegral_lintegral_swap (f := fun h ξ ↦ b h ξ * a ξ)
      (hb.mul (ha.comp measurable_snd)).aemeasurable]
    exact lintegral_congr fun ξ ↦ lintegral_mul_const' (a ξ) (b · ξ)
      ENNReal.ofReal_ne_top
  rw [schwartz_lintegral_norm_sq_fourier, hj]
  change (∫⁻ ξ, a ξ) + (2 : ℝ≥0∞)⁻¹ * (∫⁻ ξ, (∫⁻ h, b h ξ ∂μ) * a ξ) =
    ∫⁻ ξ, ENNReal.ofReal (w ξ) * a ξ
  have hhalf (ξ : ℝ) :
      (2 : ℝ≥0∞)⁻¹ * ((∫⁻ h, b h ξ ∂μ) * a ξ) =
        ENNReal.ofReal (w ξ - 1) * a ξ := by
    rw [← mul_assoc, hsymbol ξ]
  rw [← lintegral_const_mul' _ _ (by simp)]
  simp_rw [hhalf]
  rw [← lintegral_add_left ha]
  refine lintegral_congr fun ξ ↦ ?_
  have h1 : 1 ≤ w ξ := Real.one_le_rpow (le_add_of_nonneg_right (sq_nonneg _)) hs
  rw [← one_add_mul, ← ENNReal.ofReal_one, ← ENNReal.ofReal_add zero_le_one (sub_nonneg.mpr h1)]
  congr 2
  ring

end RiemannMasullo
