module

public import RiemannMasullo.ForMathlib.Analysis.Fourier.LpSpace
public import Mathlib.MeasureTheory.Function.L2Space

/-! # Parseval's identity for integrable square-integrable functions

For `f` integrable and square-integrable, the Fourier integral of `f` agrees almost everywhere
with the Fourier transform of its class in `L²` (`fourier_ae_eq_fourier_toLp`). Hence the
Fourier integrals of two such functions have the same `L²` pairing as the functions
(`integral_conj_fourier_mul_fourier`).
-/

@[expose] public section

namespace RiemannMasullo

open MeasureTheory
open scoped ContDiff ENNReal FourierTransform SchwartzMap ComplexConjugate InnerProductSpace

private theorem fourier_ae_eq_of_distribution {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
    {f : V → ℂ} (hf₁ : Integrable f) (hf₂ : MemLp f 2) (F : Lp ℂ 2 (volume : Measure V))
    (hdist : 𝓕 ((hf₂.toLp f : Lp ℂ 2 (volume : Measure V)) : 𝓢'(V, ℂ)) = (F : 𝓢'(V, ℂ))) :
    𝓕 f =ᵐ[volume] (F : V → ℂ) := by
  apply ae_eq_of_integral_contDiff_smul_eq
  · exact (VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
      (innerSL ℝ).continuous₂ hf₁).locallyIntegrable
  · exact (Lp.memLp F).locallyIntegrable one_le_two
  intro g hg hc
  let gC : V → ℂ := Complex.ofRealCLM ∘ g
  have hcC : HasCompactSupport gC := hc.comp_left rfl
  have hgC : ContDiff ℝ ∞ gC := by unfold gC; fun_prop
  let φ := hcC.toSchwartzMap hgC
  have hF := congrArg (fun T : 𝓢'(V, ℂ) ↦ T φ) hdist
  simp only [TemperedDistribution.fourier_apply, Lp.toTemperedDistribution_apply] at hF
  change (∫ x, φ x • 𝓕 f x) = ∫ x, φ x • F x
  have h1 : (∫ x, φ x • 𝓕 f x) = ∫ x, (𝓕 φ) x • f x := by
    simp_rw [smul_eq_mul, mul_comm (φ _) (𝓕 f _), mul_comm ((𝓕 φ) _) (f _),
      SchwartzMap.fourier_coe]
    simpa only [Real.instFourierTransform, FourierTransform.fourier, flip_innerₗ, smul_eq_mul]
      using VectorFourier.integral_fourierIntegral_smul_eq_flip (L := innerₗ V)
        Real.continuous_fourierChar continuous_inner hf₁ φ.integrable
  have h2 : (∫ x, (𝓕 φ) x • f x) = ∫ x, (𝓕 φ) x • hf₂.toLp f x := by
    apply integral_congr_ae
    filter_upwards [hf₂.coeFn_toLp] with x hx
    rw [hx]
  have h3 : (∫ x, (𝓕 φ) x • hf₂.toLp f x) = ∫ x, φ x • F x := hF
  exact h1.trans (h2.trans h3)

/-- On integrable square-integrable functions the Fourier integral agrees almost everywhere
with the Fourier transform on `L²`. -/
theorem fourier_ae_eq_fourier_toLp {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
    {f : V → ℂ} (hf₁ : Integrable f) (hf₂ : MemLp f 2) :
    𝓕 f =ᵐ[volume] ((𝓕 (hf₂.toLp f) : Lp ℂ 2 (volume : Measure V)) : V → ℂ) :=
  fourier_ae_eq_of_distribution hf₁ hf₂ _ (Lp.fourier_toTemperedDistribution_eq (hf₂.toLp f))

/-- Parseval's identity for two integrable square-integrable functions. -/
theorem integral_conj_fourier_mul_fourier {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
    {f g : V → ℂ} (hf₁ : Integrable f) (hf₂ : MemLp f 2)
    (hg₁ : Integrable g) (hg₂ : MemLp g 2) :
    ∫ x, conj (𝓕 f x) * 𝓕 g x = ∫ x, conj (f x) * g x := by
  have h := MeasureTheory.Lp.inner_fourier_eq (hf₂.toLp f) (hg₂.toLp g)
  rw [L2.inner_def, L2.inner_def] at h
  have h1 : ∫ x, conj (𝓕 f x) * 𝓕 g x =
      ∫ a, ⟪(𝓕 (hf₂.toLp f) : Lp ℂ 2 (volume : Measure V)) a,
        (𝓕 (hg₂.toLp g) : Lp ℂ 2 (volume : Measure V)) a⟫_ℂ := by
    apply integral_congr_ae
    filter_upwards [fourier_ae_eq_fourier_toLp hf₁ hf₂, fourier_ae_eq_fourier_toLp hg₁ hg₂]
      with x hx hy
    rw [hx, hy, RCLike.inner_apply, mul_comm]
  have h2 : ∫ x, conj (f x) * g x = ∫ a, ⟪(hf₂.toLp f) a, (hg₂.toLp g) a⟫_ℂ := by
    apply integral_congr_ae
    filter_upwards [hf₂.coeFn_toLp, hg₂.coeFn_toLp] with x hx hy
    rw [hx, hy, RCLike.inner_apply, mul_comm]
  rw [h1, h2, h]

end RiemannMasullo
