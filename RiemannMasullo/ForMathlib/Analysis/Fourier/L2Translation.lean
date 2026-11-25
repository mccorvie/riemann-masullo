module

public import RiemannMasullo.ForMathlib.Analysis.Fourier.Integrable
import Mathlib.MeasureTheory.Function.Holder
import Mathlib.MeasureTheory.Group.Integral

/-! # Translation and phase multiplication under the `L²` Fourier transform

The Fourier integral formula extends to all of `L²` by continuity and density of
Schwartz functions. This lets jump-energy arguments apply before any `L¹` bound
has been established for the function in physical space.
-/

@[expose] public noncomputable section
open MeasureTheory FourierTransform
open scoped FourierTransform SchwartzMap
namespace RiemannMasullo

/-- Translation on the real `L²` space. -/
def realL2Translation (r : ℝ) : Lp ℂ 2 (volume : Measure ℝ) →L[ℂ] Lp ℂ 2 (volume : Measure ℝ) :=
  (Lp.compMeasurePreservingₗᵢ ℂ (fun x : ℝ ↦ x + r)
    (measurePreserving_add_right volume r)).toContinuousLinearMap

/-- The translation operator agrees almost everywhere with translating representatives. -/
theorem coeFn_realL2Translation (r : ℝ) (f : Lp ℂ 2 (volume : Measure ℝ)) :
    realL2Translation r f =ᵐ[volume] fun x ↦ f (x + r) :=
  Lp.coeFn_compMeasurePreserving f (measurePreserving_add_right volume r)

/-- A Fourier phase is an essentially bounded function. -/
theorem memLp_top_realFourierPhase (r : ℝ) :
    MemLp (fun x : ℝ ↦ Complex.exp (((2 * Real.pi * r * x : ℝ) : ℂ) * Complex.I)) ⊤ := by
  apply memLp_top_of_bound (by fun_prop) 1
  exact .of_forall fun x ↦ by simp [Complex.norm_exp]

/-- The phase multiplier dual to translation on real `L²`. -/
def realL2Modulation (r : ℝ) : Lp ℂ 2 (volume : Measure ℝ) →L[ℂ] Lp ℂ 2 (volume : Measure ℝ) :=
  (ContinuousLinearMap.mul ℂ ℂ).holderL volume ⊤ 2 2 ((memLp_top_realFourierPhase r).toLp _)

/-- The modulation operator agrees almost everywhere with pointwise phase multiplication. -/
theorem coeFn_realL2Modulation (r : ℝ) (f : Lp ℂ 2 (volume : Measure ℝ)) :
    realL2Modulation r f =ᵐ[volume] fun x ↦
      Complex.exp (((2 * Real.pi * r * x : ℝ) : ℂ) * Complex.I) * f x := by
  have h := (ContinuousLinearMap.mul ℂ ℂ).coeFn_holder (r := 2) ((memLp_top_realFourierPhase r).toLp _) f
  filter_upwards [h, (memLp_top_realFourierPhase r).coeFn_toLp] with x hx hp
  simpa only [realL2Modulation, ContinuousLinearMap.holderL_apply_apply,
    ContinuousLinearMap.mul_apply', hp] using hx

private theorem fourier_translation (f : ℝ → ℂ) (r ξ : ℝ) :
    𝓕 (fun x ↦ f (x + r)) ξ =
      Complex.exp (((2 * Real.pi * r * ξ : ℝ) : ℂ) * Complex.I) * 𝓕 f ξ := by
  have h := congrFun (Fourier.fourierIntegral_comp_add_right Real.fourierChar volume f r) ξ
  simpa only [Real.fourier_real_eq, Fourier.fourierIntegral, VectorFourier.fourierIntegral,
    Function.comp_apply, LinearMap.mul_apply', Circle.smul_def, smul_eq_mul,
    Real.fourierChar_apply, mul_assoc] using h

private theorem fourier_congr_ae {f g : ℝ → ℂ} (h : f =ᵐ[volume] g) : 𝓕 f = 𝓕 g := by
  funext ξ
  simp only [Real.fourier_real_eq]
  exact integral_congr_ae (h.mono fun x hx ↦ by dsimp; rw [hx])

private theorem fourier_realL2Translation_of_integrable (r : ℝ)
    (f : Lp ℂ 2 (volume : Measure ℝ)) (hf : Integrable (f : ℝ → ℂ)) :
    𝓕 (realL2Translation r f) = realL2Modulation r (𝓕 f) := by
  have ht := coeFn_realL2Translation r f
  have hi : Integrable (realL2Translation r f : ℝ → ℂ) := by
    apply ((measurePreserving_add_right volume r).integrable_comp_of_integrable hf).congr
    simpa only [Function.comp_def] using ht.symm
  have hF := fourier_L2_coeFn_of_integrable f hf
  have hT := fourier_L2_coeFn_of_integrable (realL2Translation r f) hi
  have hM := coeFn_realL2Modulation r (𝓕 f)
  apply Lp.ext
  filter_upwards [hF, hT, hM] with ξ hFξ hTξ hMξ
  rw [hTξ, hMξ, hFξ, fourier_congr_ae ht, fourier_translation]

/-- Fourier transformation converts translation into phase multiplication on all of `L²`. -/
theorem fourier_realL2Translation (r : ℝ) (f : Lp ℂ 2 (volume : Measure ℝ)) :
    𝓕 (realL2Translation r f) = realL2Modulation r (𝓕 f) := by
  let P := fun f : Lp ℂ 2 (volume : Measure ℝ) ↦
    𝓕 (realL2Translation r f) = realL2Modulation r (𝓕 f)
  change P f
  apply DenseRange.induction_on (p := P)
    (SchwartzMap.denseRange_toLpCLM (p := 2) ENNReal.ofNat_ne_top) f
  · apply isClosed_eq
    · exact (fourierCLM ℂ (Lp ℂ 2 (volume : Measure ℝ))).continuous.comp (realL2Translation r).continuous
    · exact (realL2Modulation r).continuous.comp (fourierCLM ℂ (Lp ℂ 2 (volume : Measure ℝ))).continuous
  intro g
  apply fourier_realL2Translation_of_integrable
  exact g.integrable.congr (g.memLp 2).coeFn_toLp.symm

end RiemannMasullo
